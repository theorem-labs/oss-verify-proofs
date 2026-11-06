(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropKit.v at a529a88a618 (the plumbing of
   the property loop's block lemmas: pa_chunk8, pa_keep, pa_kwr_ro, pa_run, pa_runb, pa_branch, pa_reg, pa_leaf),
   proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at a529a88a618 (kept_run) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v
   at a529a88a618 (its section g and its tactics: the (location, value) facts of a cut, the journal-and-frame step,
   the segment's write set, the first block's bounds and pod_put, the model of a shape-7 property, the start facts
   and the input at a cut) for reac-pw/fuzz_headamp's image B: rs_ / rl_ / rm_ -> hsu_ / hd_ / hm_, role's image A
   record and code -> fuzz_headamp.asan-ubsan's (lib/AU/Img0U.v rsegs, HPgImgB.headamp_himg_B: class-4 frame of
   1024 bytes, real frame of 0x220 bytes, write set [F+0x20, F+0x278) / 116 shadow bytes / [R, R+0x198)), the block
   post HPgSteps.hdu_blk_postE in place of pa_post, one table over the four pieces of image B. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropKit.v, with its module paths, module names and numbers changed; 433 of its 529 lines of code are new or changed and 315 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Seg.v at dae3dba91f37 for reac-pw/fuzz_rate's
   image A: module paths changed; the cut vocabulary is rate's (lib/A/RtPgSeg.v, rt_ / q_ names); the segment's start
   is rate's rt_seg_pre (real frame 0x1e0 bytes) and the read-only image at a cut (w5_rom_now) is added. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW5Seg.v at a66696a9b1d1, with the helpers
   pa_E1_pp, pa_img_bounds, pa_pp_append, pa_pp_blocks, pa_R_bounds, pa_blk_bounds, pa_input_now, pa_nth_skipn,
   pa_suffix_step of proofs/reac-pw/fuzz_rate/lib/A/RtPgPropLib.v and the tactics w5_in / w5_notin / w5_kept and the
   lemma w5_ents_bounds of proofs/reac-pw/fuzz_rate/lib/A/RtPgW5CloseP.v at the same commit, for the same unit's image
   B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the cut vocabulary is lib/AU/RtPgSegB.v's (rsb_), the
   record lib/AU/RtPgImgB.v's (real frame 0x220 bytes, class-4 frame for locals of 1024 bytes, the frame's 88 shadow
   bytes, hi_w1's real-frame ranges [R, R+0x30) [R+0x58, R+0x148) [R+0x150, R+0x180) [R+0x198, R+0x1b8)) and the
   memory vocabulary lib/AU/RtPgMemB.v's (rtmb_); the prefixes w5_ / pa_ become w5b_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW5SegB.v at 2ebedbb4253d for reac-pw/fuzz_role's
   image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments lib/AU/Img0.v rsegs; the cut
   vocabulary is lib/AU/RPgSeg.v's (rs_, the run's quantities as RPgBase.rl_env's e_ fields), the record lib/AU/RPgImgA.v's
   role_himg_B (real frame 0x200 bytes, the same class-4 frame for locals and the same 88 shadow bytes, hi_w1's
   real-frame ranges [R+0x10, R+0x40) [R+0x48, R+0x160) [R+0x178, R+0x198), so w5_E1_R names [R+0x48, R+0x160)), the
   segment's start RPgCSpec.rl_seg_pre (which carries the frame's shadow and the flags byte's range), the memory
   vocabulary lib/AU/RPgMem.v's (rm_); the prefix w5b_ becomes w5_; w5_in unfolds role's location lists. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses from the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a): the bridge between the cut states of
   lib/AU/RPgSeg.v and the core lemmas of the W5 pieces (the Int-7 value pod SELI 0x81b98 -> LATCH7 0x81d88, the
   params Struct's header and count SELS 0x809d4 -> C 0x80b54 / CL 0x81ccc, its close CL 0x81ccc -> LATCH 0x81d84),
   whose start and end are stated as explicit register, cell and byte facts with a w5_post (lib/AU/RPgW5Kit.v).
   Proves no function (kind: segment lemma).
   - w5_getr5: a register named by Z_to_bv 5 r (rl_at's form) is the register named by the literal.
   - w5_at_reg / w5_at_cell: a fact of a cut's (location, value) list, read back.
   - w5_core_post: a cut's segment frame (rs_core) is carried across a piece's w5_post whose write set lies in
     the segment's.
   - w5_pre_facts: what the segment's start fixes of the real frame, the frame for locals and the first block.
   - w5_rom_now: the read-only image bytes at a cut inside the build are the image's (the segment's rom_view, kept by
     rs_core: no read-only byte lies in the callees' stack, the frame for locals, its shadow, the real frame or pp).
   - w5_input_now: an input byte at a cut and its shadow, as at the segment's start.
   - the first block's image: w5_img_buf / w5_img_flags / w5_img_gen (an image rebuilt from its parts),
     w5_pp_append (pod_put: bytes appended at len) and w5_img_close_eq (the image at the Struct's close).
   - the tactics w5_in / w5_notin / w5_kept (a location of a cut's list, a register outside a clobber list, a
     location a piece kept). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgMem RPgSeg RPgW5Kit.
Require OSSVerify.reac_pw.fuzz_role.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState}.
Lemma w5_getr5 : forall (regs : bvmap 5 word) (r : bv 5) z, bv_unsigned r = z -> getr regs (Z_to_bv 5 z) = getr regs r.
Proof.
intros regs r z H. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. subst z.
unfold bv_wrap. apply Z.mod_small. pose proof (bv_unsigned_in_range 5 r) as Hr. exact Hr.
Qed.
End a.

(* ======================================== byte lists ======================================== *)
Lemma w5_nth_ow : forall (l bs : list byte) off j d, (off + length bs <= length l)%nat ->
nth j (overwrite l off bs) d = if ((off <=? j) && (j <? off + length bs))%nat then nth (j - off) bs d else nth j l d.
Proof.
intros l bs off j d Hl. unfold overwrite.
assert (Hf : length (firstn off l) = off) by (apply firstn_length_le; lia).
destruct (Nat.leb_spec off j) as [H1|H1]; cbn [andb].
- rewrite app_nth2 by lia. rewrite Hf.
  destruct (Nat.ltb_spec j (off + length bs)) as [H2|H2].
  + rewrite app_nth1 by lia. reflexivity.
  + rewrite app_nth2 by lia. rewrite nth_skipn. f_equal. lia.
- rewrite app_nth1 by lia. rewrite nth_firstn. destruct (Nat.ltb_spec j off); [reflexivity | lia].
Qed.
Lemma w5_len_ow : forall (l bs : list byte) off, (off + length bs <= length l)%nat ->
length (overwrite l off bs) = length l.
Proof. intros l bs off H. apply length_overwrite. exact H. Qed.

Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* bytes rebuilt pointwise: the ones Pb marks are read off the new state, the others are the old list's and
   unchanged in memory *)
Lemma w5_bytes_merge : forall H mem H' mem' a (l l' : list byte) (Pb : Z -> bool),
rm_bytes rsegs H mem a l -> length l' = length l ->
(forall j, (j < length l)%nat -> Pb (a + Z.of_nat j) = false ->
  aview rsegs H' mem' (a + Z.of_nat j) = aview rsegs H mem (a + Z.of_nat j) /\
  nth j l' (Z_to_bv 8 0) = nth j l (Z_to_bv 8 0)) ->
(forall j, (j < length l)%nat -> Pb (a + Z.of_nat j) = true ->
  aview rsegs H' mem' (a + Z.of_nat j) = Some (bv_unsigned (nth j l' (Z_to_bv 8 0)))) ->
rm_bytes rsegs H' mem' a l'.
Proof.
intros H mem H' mem' a l l' Pb Hb Hlen Hout Hin. apply rm_bytes_aview. intros j Hj. rewrite Hlen in Hj.
destruct (Pb (a + Z.of_nat j)) eqn:E; [exact (Hin j Hj E)|].
destruct (Hout j Hj E) as [A N]. rewrite A, N. exact (proj1 (rm_bytes_aview rsegs H mem a l) Hb j Hj).
Qed.
End m.

(* ======================================== the record ======================================== *)
Lemma w5_find_none : forall (f : Z * pval -> bool) ps, existsb f ps = false -> find f ps = None.
Proof.
intros f ps. induction ps as [|x ps IH]; cbn; [reflexivity|].
intros H. apply orb_false_iff in H as [H1 H2]. rewrite H1. exact (IH H2).
Qed.
Lemma w5_find_some : forall (f : Z * pval -> bool) ps, existsb f ps = true -> exists x, find f ps = Some x.
Proof.
intros f ps. induction ps as [|x ps IH]; cbn; [discriminate|].
intros H. destruct (f x) eqn:E; [exists x; reflexivity|]. apply IH. exact H.
Qed.
Lemma w5_first1 : forall ps, rs_first ps = 1 -> first_params ps = None.
Proof.
intros ps H. unfold rs_first in H. unfold first_params.
destruct (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps) eqn:E; cbn in H; [discriminate|].
rewrite (w5_find_none _ ps E). reflexivity.
Qed.
Lemma w5_first0 : forall ps, rs_first ps <> 1 -> exists v, first_params ps = Some v.
Proof.
intros ps H. unfold rs_first in H. unfold first_params.
destruct (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps) eqn:E; cbn in H; [|lia].
destruct (w5_find_some _ ps E) as (x & Hx). rewrite Hx. exists (snd x). reflexivity.
Qed.
Lemma w5_first_range : forall ps, rs_first ps = 0 \/ rs_first ps = 1.
Proof. intros ps. unfold rs_first. destruct (negb _); cbn; lia. Qed.
Lemma w5_plen_lo : forall sh ps, sh <> 7 -> 16 <= rs_plen sh ps.
Proof.
intros sh ps Hsh. unfold rs_plen, pc_buf, body_bytes, hdr_bytes, open_bytes. cbn [pc_shape pc_props pc_open].
replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact Hsh).
rewrite !app_nil_r, !zlen_app, !zlen_le32. pose proof (Zle_0_nat (length (flat_map (prop_bytes sh) ps))). lia.
Qed.
Lemma w5_buf_open_len : forall sh ps es,
Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) =
rs_plen sh ps + 16 + Z.of_nat (length (flat_map enc_pod es)).
Proof.
intros sh ps es. unfold rs_plen, pc_buf, open_bytes. cbn [pc_shape pc_props pc_open].
rewrite app_nil_r, !zlen_app, !zlen_le32. lia.
Qed.
(* the bounds of the first block's image at a property cut *)
Lemma w5_img_bounds : forall sh ps, rs_wf sh ps -> (length ps <= 2)%nat ->
Z.of_nat (length (pc_buf (PbCut sh ps None))) + 16 <= 5440 /\
Z.of_nat (length (pc_buf (PbCut sh ps None))) mod 8 = 0 /\
(length (pc_ents (PbCut sh ps None)) <= 32)%nat /\
Forall (fun e => (length (e_body e) <= 96)%nat) (pc_ents (PbCut sh ps None)).
Proof.
intros sh ps (Hs & Hk & He & Hl) H2.
assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hk]; intros kv [_ X]; exact X).
destruct (pc_buf_len_none sh ps Hv He) as [L1 [c Hc]].
assert (EW : (length (pc_ents (PbCut sh ps None)) <= 32)%nat /\ Forall ent_wf (pc_ents (PbCut sh ps None))).
{ unfold pc_ents. cbn [pc_props pc_open].
  destruct (first_params ps) as [[iv|es]|] eqn:E; try (split; [cbn; lia | constructor]).
  unfold first_params in E. destruct (find _ _) as [kv|] eqn:F; [|discriminate]. cbn in E. injection E as E.
  apply find_some in F as [Hin _]. split.
  - rewrite Forall_forall in Hk. destruct (Hk kv Hin) as [_ Hv']. rewrite E in Hv'. exact Hv'.
  - apply all_ents_Forall in He. rewrite Forall_forall in He. specialize (He kv Hin). rewrite E in He. exact He. }
destruct EW as [E1 E2].
split; [lia|]. split; [rewrite Hc; apply Z_mod_mult|]. split; [exact E1|].
eapply Forall_impl; [|exact E2]. intros e (_ & Hb & Hz). rewrite Hb. lia.
Qed.
(* the entries' bounds of an image, with or without an open Struct *)
Lemma w5_ents_bounds : forall sh ps o, rs_wf sh ps ->
(match o with Some es => Forall ent_wf es /\ (length es <= 32)%nat | None => True end) ->
(length (pc_ents (PbCut sh ps o)) <= 32)%nat /\ Forall (fun e => (length (e_body e) <= 96)%nat) (pc_ents (PbCut sh ps o)).
Proof.
intros sh ps o (Hs & Hk & He & Hl) Ho.
assert (Hbody : forall l, Forall ent_wf l -> Forall (fun e => (length (e_body e) <= 96)%nat) l).
{ intros l Hl'. eapply Forall_impl; [|exact Hl']. intros e (_ & Hb & Hz). rewrite Hb. lia. }
unfold pc_ents. cbn [pc_props pc_open].
destruct (first_params ps) as [[iv|es']|] eqn:E.
- split; [cbn; lia | constructor].
- unfold first_params in E. destruct (find _ _) as [kv|] eqn:F; [|discriminate]. cbn in E. injection E as E.
  apply find_some in F as [Hin _].
  rewrite Forall_forall in Hk. destruct (Hk kv Hin) as [_ Hv']. rewrite E in Hv'. cbn in Hv'.
  split; [exact Hv'|]. apply Hbody.
  apply all_ents_Forall in He. rewrite Forall_forall in He. specialize (He kv Hin). rewrite E in He. exact He.
- destruct o as [es|]; [destruct Ho as [Ho1 Ho2]; split; [exact Ho2 | apply Hbody; exact Ho1] |
  split; [cbn; lia | constructor]].
Qed.

(* ---- the input's cursor after one byte read ---- *)
Lemma w5_nth_skipn : forall (l : list byte) j bb r, skipn j l = bb :: r ->
(j < length l)%nat /\ nth j l (Z_to_bv 8 0) = bb.
Proof.
induction l as [|x l IH]; intros j bb r H; destruct j as [|j]; cbn [skipn length nth] in *; try discriminate.
- injection H as <- <-. split; [lia | reflexivity].
- destruct (IH j bb r H) as [H1 H2]. split; [lia | exact H2].
Qed.
Lemma w5_suffix_step : forall rest r, rs_suffix rest r -> rs_suffix rest (snd (fuzz_u8 r)).
Proof.
intros rest r (j & Hj & ->). destruct (skipn j rest) as [|bb r'] eqn:E; cbn [fuzz_u8 snd].
- exists j. split; [exact Hj | symmetry; exact E].
- destruct (w5_nth_skipn rest j bb r' E) as [Hjl _]. exists (S j). split; [lia|].
  replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, E. reflexivity.
Qed.

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

(* ---- the segment's write set: the real frame's cells [R+0x48, R+0x160) (hi_w1's fourth range), the frame for
   locals F+0x20 .. F+0x278 (its first), the frame's shadow bytes 4 .. 78 (its second) and the first block ---- *)
Lemma w5_E1_R : forall cx a, e_R (x_e cx) + 0x48 <= a < e_R (x_e cx) + 0x160 -> rs_E1 rsegs cx a.
Proof.
intros cx a Ha. left. unfold rl_inw. cbn [hi_w1 role_himg_B].
apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rl_xv]. lia.
Qed.
Lemma w5_E1_F : forall cx a, e_F (x_e cx) + 0x20 <= a < e_F (x_e cx) + 0x278 -> rs_E1 rsegs cx a.
Proof.
intros cx a Ha. left. unfold rl_inw. cbn [hi_w1 role_himg_B]. apply Exists_cons_hd. cbn [fst snd rl_xv]. lia.
Qed.
Lemma w5_E1_fsh : forall cx a, shadow_addr (e_F (x_e cx)) + 4 <= a < shadow_addr (e_F (x_e cx)) + 79 ->
rs_E1 rsegs cx a.
Proof.
intros cx a Ha. left. unfold rl_inw. cbn [hi_w1 role_himg_B].
apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rl_xv]. lia.
Qed.
Lemma w5_E1_pp : forall cx a, e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE -> rs_E1 rsegs cx a.
Proof. intros cx a Ha. right. exact Ha. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

Lemma w5_at_reg : forall H mem regs e (L : list (rl_loc * Z)) r v,
rs_at rsegs H mem regs e L -> In (LReg r, v) L -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros H mem regs e L r v HL Hin. exact (proj1 (Forall_forall _ _) HL _ Hin). Qed.
Lemma w5_at_cell : forall H mem regs e (L : list (rl_loc * Z)) o v,
rs_at rsegs H mem regs e L -> In (LCell XR o, v) L ->
val_mem rsegs (mrestrict H mem) (e_R e + o) 8 (v mod 2 ^ 64).
Proof. intros H mem regs e L o v HL Hin. exact (proj1 (Forall_forall _ _) HL _ Hin). Qed.

(* the cut's segment frame across a piece *)
Lemma w5_core_post : forall cx (E1 Ep : Z -> Prop) ly2 S2 W2 regs2 mem2 md2 pc clob
  (R : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop) W3 c3,
  rs_core rsegs B MT cx E1 ly2 S2 W2 regs2 mem2 md2 ->
  (forall a, Ep a -> E1 a) ->
  (forall r, (r = 2 \/ r = 3 \/ r = 4) -> ~ In (Z_to_bv 5 r) clob) ->
  w5_post B MT (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    (x_k cx) regs2 ly2 S2 W2 mem2 md2 pc clob Ep R W3 c3 ->
  exists ly3 S3 regs3 mem3 md3, c3 = cfg_at rsegs pc regs3 mem3 md3 /\
    rs_core rsegs B MT cx E1 ly3 S3 W3 regs3 mem3 md3 /\
    (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs3 r = getr regs2 r) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs2 - T_SEG_STK <= a < spZ regs2) -> ~ Ep a ->
     aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) /\
    R W3 regs3 mem3.
Proof using MTL.
intros cx E1 Ep ly2 S2 W2 regs2 mem2 md2 pc clob R W3 c3 Hcore HE Hc
  (ly3 & S3 & regs3 & mem3 & md3 & Hcfg & HJ3 & Hregs & Hfr & Hperm & Hio & Hmo & Hmem & HR).
destruct Hcore as (HJ2 & Hr234 & Hfr2 & Hperm2 & Hio2 & Hmo2 & Hmem2).
assert (Hsp : spZ regs2 = spZ (x_regs cx)).
{ unfold spZ. rewrite <- !(w5_getr5 _ 2%bv 2) by reflexivity. rewrite (Hr234 2); [reflexivity | lia]. }
exists ly3, S3, regs3, mem3, md3. split; [exact Hcfg|].
split.
{ split; [exact HJ3|]. split.
  { intros r Hr. rewrite Hregs; [apply Hr234; exact Hr| |apply Hc; exact Hr].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. destruct Hr as [-> | [-> | ->]]; vm_compute; discriminate. }
  split; [rewrite Hfr; exact Hfr2|].
  split; [eapply Permutation_trans; [exact Hperm | exact Hperm2]|].
  split; [eapply same_io_trans; [exact Hio2 | exact Hio]|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo2 Hmo)|].
  intros a Ha Hst HnE. rewrite (Hmem a Ha); [apply Hmem2; assumption | rewrite Hsp; exact Hst |].
  intros HEp. exact (HnE (HE a HEp)). }
split; [exact Hregs|]. split; [exact Hmem | exact HR].
Qed.
End b.

(* ======================================== the segment's start ======================================== *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws rsegs B.
(* the real frame, the frame for locals (class 4: 1024 bytes) and the first block, as the segment's start fixes
   them *)
Lemma w5_pre_facts : forall cx, rs_pre rsegs B cx ->
  x_sp0 cx - x_STK cx <= e_R (x_e cx) - T_SEG_STK /\ e_R (x_e cx) + 0x200 <= x_sp0 cx /\
  e_R (x_e cx) mod 16 = 0 /\ getr (x_regs cx) 2 = w64 (e_R (x_e cx)) /\
  alloc_ceiling + T_SEG_STK <= e_R (x_e cx) /\ x_sp0 cx <= 2 ^ 47 /\
  In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_lyc cx) (x_Sc cx)) /\
  ~ In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_ly cx) (x_S cx)) /\
  4096 <= e_pp (x_e cx) /\ e_pp (x_e cx) + Layout.PP_SIZE <= alloc_ceiling /\
  4096 <= e_F (x_e cx) /\ e_F (x_e cx) + 1024 <= alloc_ceiling /\ in_app (e_pp (x_e cx)) Layout.PP_SIZE.
Proof using LAWS.
intros cx Hpre. unfold rs_pre, rl_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & HR16 & HRs & HRstk & Hown & HF & Hfsh & Hpp0 & Hpp & Hfl & Hro &
  Hglobs & Hrz & Hstrs & Hcells & Hrom & Hout).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HST0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp) as (_ & Hp4096 & Hpceil & Happ & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Hpceil, Happ.
assert (Hin : In (hi_cid role_himg_B, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HAR Hin) as (F1 & F2 & _).
rewrite <- HF in F1, F2. cbn [hi_cid role_himg_B] in F2. change (fs_frame_bytes 4) with 1024 in F2.
pose proof asan_consts as (C1 & _). cbn [hi_rsz role_himg_B] in HRs.
unfold T_SEG_STK, ASTACK in *.
split; [lia|]. split; [lia|]. split; [exact HR16|]. split; [exact H2|]. split; [lia|]. split; [lia|].
split; [exact Hpp|]. split; [exact Hout|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. exact Happ.
Qed.
(* the frame for locals lies in the application range (class 4: 1024 bytes) *)
Lemma w5_frame_app : forall cx, rs_pre rsegs B cx -> in_app (e_F (x_e cx)) 1024.
Proof using LAWS.
intros cx Hpre. unfold rs_pre, rl_seg_pre in Hpre.
destruct Hpre as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & HF & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (hi_cid role_himg_B, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & F3).
rewrite <- HF in F3. cbn [hi_cid role_himg_B] in F3. change (fs_frame_bytes 4) with 1024 in F3. exact F3.
Qed.

(* the first block at the segment's start: live, made since the journal's start, in application memory *)
Lemma w5_pp_blocks : forall cx, rs_pre rsegs B cx ->
In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_lyc cx) (x_Sc cx)) /\
~ In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_ly cx) (x_S cx)) /\
amem_range (e_pp (x_e cx)) Layout.PP_SIZE.
Proof using LAWS.
intros cx Hpre. unfold rs_pre, rl_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & HR16 & HRs & HRstk & Hown & HF & Hfsh & Hpp0 & Hpp & Hfl & Hro &
  Hglobs & Hrz & Hstrs & Hcells & Hrom & Hout).
split; [exact Hpp|]. split; [exact Hout|].
eapply (amem_range_of_block rsegs B LAWS); [exact (proj1 HJ) | exact Hpp | lia | reflexivity].
Qed.

(* the read-only image at a cut of the build: the segment's rom_view, kept by rs_core *)
Lemma w5_rom_now : forall cx ly2 S2 W2 regs2 mem2 md2,
  rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
  rom_view rsegs W2 mem2.
Proof using LAWS.
intros cx ly2 S2 W2 regs2 mem2 md2 Hpre Hcore.
pose proof (w5_pre_facts cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & Ppin & Ppout & PB1 & PB2 & FB1 & FB2 & PApp).
pose proof Hpre as Hpre'. unfold rs_pre, rl_seg_pre in Hpre'.
destruct Hpre' as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & HF & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrom & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (hi_cid role_himg_B, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct Hcore as (_ & _ & _ & _ & _ & _ & Hmem).
pose proof ASAN_CEIL_range as ([AC1 AC2] & _). unfold ASAN_CEIL in AC1, AC2.
assert (HTS : T_SEG_STK = 16384) by reflexivity.
intros a Ha. pose proof Ha as (sg & Hsg & _ & Hr).
assert (Himg : in_img rsegs a) by (exists sg; split; [exact Hsg | exact Hr]).
pose proof (w5_segs_low a Himg) as Hlow.
assert (Hsp : spZ (x_regs cx) = e_R (x_e cx)) by (unfold spZ; rewrite RB4; unfold w64; apply unsigned_lit_small; lia).
unfold kLowMemEnd in Hlow.
rewrite (Hmem a); [exact (Hrom a Ha) | lia | rewrite Hsp; unfold T_SEG_STK, ASTACK in *; lia |].
(* a read-only byte is no byte of the segment's write set: pp and the frame for locals are client memory, which no
   image byte is (AR_client_img_law); the frame's shadow and the real frame lie above the image *)
intros [Hw | Hp].
- unfold rl_inw in Hw. cbn [hi_w1 role_himg_B] in Hw.
  apply Exists_cons in Hw as [Hw | Hw]; cbn [fst snd rl_xv] in Hw.
  { (* the frame for locals F + 0x20 .. F + 0x278 *)
    assert (Hc : exists cid pos, In (cid, pos) (frames (x_Sc cx)) /\
      frame_addr (x_lyc cx) cid pos <= a < frame_addr (x_lyc cx) cid pos + fs_frame_bytes cid).
    { exists (hi_cid role_himg_B), (x_pos cx). split; [exact Hin|].
      rewrite <- HF. cbn [hi_cid role_himg_B]. change (fs_frame_bytes 4) with 1024. lia. }
    destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR (or_intror (or_introl Hc))) as [_ Hni].
    exact (Hni Himg). }
  apply Exists_cons in Hw as [Hw | Hw]; cbn [fst snd rl_xv] in Hw.
  { unfold shadow_addr, SHADOW_OFF in Hw. pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia)). lia. }
  repeat (apply Exists_cons in Hw as [Hw | Hw];
    [cbn [fst snd rl_xv] in Hw; unfold T_SEG_STK, ASTACK in *; lia |]).
  apply Exists_nil in Hw. exact Hw.
- assert (Hc : exists p n, In (p, n) (ablocks B (x_lyc cx) (x_Sc cx)) /\ p <= a < p + req_size n).
  { exists (e_pp (x_e cx)), Layout.PP_SIZE. split; [exact Ppin|]. change (req_size Layout.PP_SIZE) with 19744.
    unfold Layout.PP_SIZE in Hp. lia. }
  destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR (or_introl Hc)) as [_ Hni].
  exact (Hni Himg).
Qed.

(* the input at a cut of the build: its bytes and their shadow as at the segment's start (rs_in) *)
Lemma w5_input_now : forall cx rest ly2 S2 W2 regs2 mem2 md2 c,
rs_pre rsegs B cx -> rl_fsh rsegs (w_H (x_W cx)) (x_memc cx) (e_F (x_e cx)) (hi_shA role_himg_B) ->
rs_in rsegs cx rest -> rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
rs_fsh_at rsegs cx W2 mem2 rs_P0 -> 0 <= c < Z.of_nat (length rest) ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_src (x_e cx) + c) 1 (nth (Z.to_nat c) (rs_u8s rest) 0) /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (e_src (x_e cx) + c) 1.
Proof using LAWS.
intros cx rest ly2 S2 W2 regs2 mem2 md2 c Hpre Hfsh0 Hin Hcore Hfsh Hc.
pose proof (w5_pre_facts cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & Ppin & Ppout & PB1 & PB2 & FB1 & FB2 & PApp).
pose proof (w5_frame_app cx Hpre) as FB3.
pose proof (w5_pp_blocks cx Hpre) as (_ & _ & PA).
assert (PA' : e_pp (x_e cx) + Layout.PP_SIZE <= 0x7fff7fff \/ 0x10007fff8000 <= e_pp (x_e cx))
  by (destruct PA as [A|[A _]]; [left; exact A | right; exact A]). clear PA.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ASAN_CEIL_range as ([AC1 AC2] & _). unfold ASAN_CEIL in AC1, AC2.
assert (HTS : T_SEG_STK = 16384) by reflexivity.
destruct Hin as (Hleft & Hgarr & Hra & Hhull & Hamr & Hsrc0 & Hsrcn & Hapart).
destruct Hcore as (_ & _ & _ & _ & _ & _ & Hkm).
assert (SP : spZ (x_regs cx) = e_R (x_e cx)) by (unfold spZ; rewrite RB4; unfold w64; apply unsigned_lit_small; lia).
rewrite SP in Hkm.
set (src := e_src (x_e cx)) in *.
(* the byte *)
assert (Ka : forall a, src <= a < src + e_left (x_e cx) ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).
{ intros a Ha. destruct (Hapart a Ha) as (N1 & N2 & N3). apply Hkm; [lia | exact N1 |].
  intros [X|X]; [exact (N2 X) | exact (N3 X)]. }
split.
- destruct (Hgarr (Z.to_nat c) ltac:(unfold rs_u8s; rewrite length_map; lia)) as [V _]. rewrite Z2Nat.id in V by lia.
  eapply val_mem_kept; [|exact V]. intros k Hk. apply Ka. lia.
- pose proof (rm_in_ra _ _ _ _ c Hra ltac:(lia)) as R1. fold src in R1.
  intros y Hy. destruct (R1 y Hy) as (sv & Hs & Hok). exists sv. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr.
  assert (Y8 : 0 <= y / 8 < 2 ^ 44) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr;
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  set (sa := SHADOW_OFF + y / 8).
  destruct (Z_lt_le_dec sa (shadow_addr (e_F (x_e cx)))) as [Lo|Lo];
  [| destruct (Z_lt_le_dec sa (shadow_addr (e_F (x_e cx)) + 88)) as [Hi|Hi]].
  2:{ unfold rs_fsh_at, rl_fsh in Hfsh, Hfsh0.
      replace sa with (shadow_addr (e_F (x_e cx)) + (sa - shadow_addr (e_F (x_e cx)))) by lia.
      rewrite (Hfsh (sa - shadow_addr (e_F (x_e cx))) ltac:(replace (Z.of_nat (length rs_P0)) with 88 by reflexivity; lia)).
      rewrite (Hfsh0 (sa - shadow_addr (e_F (x_e cx))) ltac:(rewrite <- rm_sh_P0; rewrite rm_sh_len; lia)).
      rewrite <- rm_sh_P0. reflexivity. }
  all: apply Hkm; [unfold sa, SHADOW_OFF; lia | unfold sa, SHADOW_OFF, T_SEG_STK, ASTACK in *; lia |].
  all: intros [X|X]; [unfold rl_inw in X; cbn [hi_w1 role_himg_B] in X;
       repeat (apply Exists_cons in X as [X|X]; [cbn [fst snd rl_xv] in X|]); [..|apply Exists_nil in X; exact X] | ].
  all: unfold sa, shadow_addr, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, amem_range, kLowMemEnd, kHighMemEnd, Layout.PP_SIZE in *; lia.
Qed.
End s.

(* ======================================== the first block's image ======================================== *)
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* buf[0..len) of an image *)
Lemma w5_img_buf : forall H mem pp b isp hp pst es corr,
rm_bytes rsegs H mem pp (pp_image b isp hp pst es corr) -> rm_bytes rsegs H mem pp b.
Proof. intros H mem pp b isp hp pst es corr Hb. rewrite pp_image_tail in Hb. apply rm_bytes_app in Hb as [Hb _]. exact Hb. Qed.
(* the two flag words of an image, carried to a state that keeps them *)
Lemma w5_img_flags : forall H mem H' mem' pp b isp hp pst es corr,
Z.of_nat (length b) <= POD_BUF_MAX -> (length es <= 32)%nat -> Forall (fun e => (length (e_body e) <= 96)%nat) es ->
rm_bytes rsegs H mem pp (pp_image b isp hp pst es corr) ->
(forall y, pp + OFF_HAS_PARAMS <= y < pp + OFF_ENT -> aview rsegs H' mem' y = aview rsegs H mem y) ->
rm_bytes rsegs H' mem' (pp + OFF_HAS_PARAMS) (le32 (Z.b2z hp)) /\
rm_bytes rsegs H' mem' (pp + OFF_PARAMS_STRUCT) (le32 (Z.b2z pst)).
Proof.
intros H mem H' mem' pp b isp hp pst es corr Hb He Hs Old K.
pose proof (rm_pp_has_params rsegs b isp hp pst es corr Hb He Hs H mem pp Old) as V1.
pose proof (rm_pp_params_struct rsegs b isp hp pst es corr Hb He Hs H mem pp Old) as V2.
split; (eapply rm_bytes_kept; [apply rm_bytes_of_val; eassumption|]);
  intros y Hy; rewrite ?length_le32, ?length_Z_to_le_bytes in Hy; apply K; unfold OFF_HAS_PARAMS, OFF_PARAMS_STRUCT, OFF_ENT in *; lia.
Qed.
(* an image rebuilt from its parts: buf[0..len) grown or patched (b'), len, the two flag words, every other byte
   kept from the old image (the zeros after b', is_props, the entries and what follows them) *)
Lemma w5_img_gen : forall H mem H' mem' pp b b' isp hp pst hp' pst' es corr,
(length b <= length b')%nat -> Z.of_nat (length b') <= POD_BUF_MAX -> (length es <= 32)%nat ->
Forall (fun e => (length (e_body e) <= 96)%nat) es ->
rm_bytes rsegs H mem pp (pp_image b isp hp pst es corr) ->
rm_bytes rsegs H' mem' pp b' ->
val_mem rsegs (mrestrict H' mem') (pp + OFF_LEN) 8 (Z.of_nat (length b')) ->
rm_bytes rsegs H' mem' (pp + OFF_HAS_PARAMS) (le32 (Z.b2z hp')) ->
rm_bytes rsegs H' mem' (pp + OFF_PARAMS_STRUCT) (le32 (Z.b2z pst')) ->
(forall y, pp + Z.of_nat (length b') <= y < pp + OFF_LEN \/ pp + OFF_IS_PROPS <= y < pp + OFF_HAS_PARAMS \/
  pp + OFF_ENT <= y < pp + PP_SIZE -> aview rsegs H' mem' y = aview rsegs H mem y) ->
rm_bytes rsegs H' mem' pp (pp_image b' isp hp' pst' es corr).
Proof.
intros H mem H' mem' pp b b' isp hp pst hp' pst' es corr Hbb Hb' He Hs Old Nb Nlen Nh Np K.
assert (Hb : Z.of_nat (length b) <= POD_BUF_MAX) by lia.
pose proof (length_pp_image b isp hp pst es corr Hb He Hs) as LI.
rewrite pp_image_tail in LI, Old |- *. unfold pp_tail in LI, Old |- *.
remember (flat_map ent_mem es ++ zeros (Z.to_nat (ENT_SIZE * (POD_ENT_MAX - Z.of_nat (length es))))
  ++ le32 (Z.of_nat (length es)) ++ le32 (Z.b2z corr) ++ zeros 4) as T eqn:ET.
clear ET.
assert (Ez : zeros (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b)))
  = zeros (length b' - length b) ++ zeros (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b')))).
{ rewrite <- zeros_app. f_equal. unfold POD_BUF_MAX in *. lia. }
rewrite Ez in Old, LI. rewrite <- app_assoc in Old.
rewrite !length_app, !length_zeros, length_le64, !length_le32 in LI.
unfold PP_SIZE, POD_BUF_MAX in *.
apply rm_bytes_app in Old as [_ Old]. apply rm_bytes_app in Old as [_ Old].
apply rm_bytes_app in Old as [Ozk Old]. apply rm_bytes_app in Old as [_ Old].
apply rm_bytes_app in Old as [Oi Old]. apply rm_bytes_app in Old as [_ Old].
apply rm_bytes_app in Old as [_ OT].
repeat (first [rewrite length_zeros in Ozk | rewrite length_zeros in Oi | rewrite length_zeros in OT |
  rewrite length_le64 in Oi | rewrite length_le64 in OT | rewrite length_le32 in OT]).
apply rm_bytes_app. split; [exact Nb|].
apply rm_bytes_app. split.
{ eapply rm_bytes_kept.
  - replace (pp + Z.of_nat (length b')) with (pp + Z.of_nat (length b) + Z.of_nat (length b' - length b)) by lia.
    exact Ozk.
  - intros y Hy. rewrite length_zeros in Hy. apply K. left. unfold OFF_LEN. lia. }
rewrite length_zeros.
apply rm_bytes_app. split.
{ unfold le64. apply rm_bytes_of_val.
  replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b')))) with (pp + OFF_LEN)
    by (unfold OFF_LEN; lia). exact Nlen. }
rewrite length_le64.
apply rm_bytes_app. split.
{ eapply rm_bytes_kept.
  - replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8)
      with (pp + Z.of_nat (length b) + Z.of_nat (length b' - length b) +
            Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8) by lia.
    exact Oi.
  - intros y Hy. rewrite length_le32 in Hy. apply K. right. left. unfold OFF_IS_PROPS, OFF_HAS_PARAMS. lia. }
rewrite length_le32.
apply rm_bytes_app. split.
{ replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8 + Z.of_nat 4)
    with (pp + OFF_HAS_PARAMS) by (unfold OFF_HAS_PARAMS; lia). exact Nh. }
rewrite length_le32.
apply rm_bytes_app. split.
{ replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8 + Z.of_nat 4
    + Z.of_nat 4) with (pp + OFF_PARAMS_STRUCT) by (unfold OFF_PARAMS_STRUCT; lia). exact Np. }
rewrite length_le32.
eapply rm_bytes_kept.
- replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8 + Z.of_nat 4
    + Z.of_nat 4 + Z.of_nat 4)
    with (pp + Z.of_nat (length b) + Z.of_nat (length b' - length b) +
          Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4) by lia.
  exact OT.
- intros y Hy. apply K. right. right. unfold OFF_ENT. lia.
Qed.

(* pod_put into the first block (pod.h:175-182): x appended at len, len := len + |x|, every other byte kept
   [Layout.pp_image_put] *)
Lemma w5_pp_append : forall H mem H' mem' pp b x isp hasp pst es corr,
Z.of_nat (length b + length x) <= Layout.POD_BUF_MAX -> (length es <= 32)%nat ->
Forall (fun e => (length (e_body e) <= 96)%nat) es ->
rm_bytes rsegs H mem pp (pp_image b isp hasp pst es corr) ->
rm_bytes rsegs H' mem' (pp + Z.of_nat (length b)) x ->
val_mem rsegs (mrestrict H' mem') (pp + Layout.OFF_LEN) 8 (Z.of_nat (length b + length x)) ->
(forall y, pp <= y < pp + Layout.PP_SIZE ->
 ~ (pp + Z.of_nat (length b) <= y < pp + Z.of_nat (length b) + Z.of_nat (length x)) ->
 ~ (pp + Layout.OFF_LEN <= y < pp + Layout.OFF_LEN + 8) -> aview rsegs H' mem' y = aview rsegs H mem y) ->
rm_bytes rsegs H' mem' pp (pp_image (b ++ x) isp hasp pst es corr).
Proof.
intros H mem H' mem' pp b x isp hasp pst es corr Hbx Hes Hbod Old Nx Nlen K.
pose proof (length_pp_image b isp hasp pst es corr ltac:(unfold Layout.POD_BUF_MAX in Hbx; lia) Hes Hbod) as LI.
rewrite pp_image_tail in LI, Old |- *. set (T := pp_tail isp hasp pst es corr) in *.
set (k := Z.to_nat (Layout.POD_BUF_MAX - Z.of_nat (length (b ++ x)))).
assert (Ez : zeros (Z.to_nat (Layout.POD_BUF_MAX - Z.of_nat (length b))) = zeros (length x) ++ zeros k).
{ rewrite <- zeros_app. f_equal. unfold k. rewrite length_app. unfold Layout.POD_BUF_MAX in Hbx |- *. lia. }
assert (Hk : Z.of_nat (length b) + Z.of_nat (length x) + Z.of_nat k = 16384).
{ unfold k. rewrite length_app. unfold Layout.POD_BUF_MAX in Hbx |- *. lia. }
clearbody k T.
rewrite Ez in Old, LI.
rewrite !length_app, !length_zeros, length_le64 in LI.
apply rm_bytes_app in Old as [Ob Old]. rewrite <- app_assoc in Old.
apply rm_bytes_app in Old as [_ Old]. apply rm_bytes_app in Old as [Ozk Old].
apply rm_bytes_app in Old as [_ OT].
rewrite length_zeros in Ozk, OT. rewrite length_zeros, length_le64 in OT.
rewrite <- app_assoc. apply rm_bytes_app. split.
{ eapply (rm_bytes_kept rsegs); [exact Ob|]. intros y Hy. apply K; unfold Layout.PP_SIZE, Layout.OFF_LEN in *; lia. }
apply rm_bytes_app. split; [exact Nx|].
apply rm_bytes_app. split.
{ eapply (rm_bytes_kept rsegs); [exact Ozk|]. intros y Hy. rewrite length_zeros in Hy.
  apply K; unfold Layout.PP_SIZE, Layout.OFF_LEN in *; lia. }
rewrite length_zeros. apply rm_bytes_app. split.
{ unfold le64. apply rm_bytes_of_val.
  replace (pp + Z.of_nat (length b) + Z.of_nat (length x) + Z.of_nat k) with (pp + Layout.OFF_LEN)
    by (unfold Layout.OFF_LEN; lia).
  rewrite length_app. exact Nlen. }
rewrite length_le64. eapply (rm_bytes_kept rsegs).
- replace (pp + Z.of_nat (length b) + Z.of_nat (length x) + Z.of_nat k + Z.of_nat 8)
    with (pp + Z.of_nat (length b) + Z.of_nat (length x) + Z.of_nat k + 8) by lia. exact OT.
- intros y Hy. apply K; unfold Layout.PP_SIZE, Layout.OFF_LEN in *; lia.
Qed.

(* the image at the Struct's close (Model.pc_buf_close; pod.h:434-438): the size word patched, and the two flag
   words set when this Struct is the first params property *)
Lemma w5_img_close_eq : forall sh ps es, sh <> 7 ->
pc_image (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None) =
pp_image (overwrite (pc_buf (PbCut sh ps (Some es))) (Z.to_nat (rs_at_of sh ps))
           (le32 (Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) - rs_at_of sh ps - 8)))
  (is_props (PodRec sh ps None))
  (has_params (PodRec sh ps None) || (rs_first ps =? 1))
  (params_struct (PodRec sh ps None) || (rs_first ps =? 1))
  (pc_ents (PbCut sh ps (Some es))) false.
Proof.
intros sh ps es Hsh. unfold pc_image. cbn [pc_shape pc_props pc_open].
change (pc_buf (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None))
  with (pc_buf (pc_close (PbCut sh ps (Some es)))).
rewrite <- (pc_buf_close sh ps es Hsh).
replace (Z.to_nat (rs_at_of sh ps)) with (length (pc_buf (PbCut sh ps None)) + 8)%nat
  by (unfold rs_at_of, rs_plen; lia).
replace (Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) - rs_at_of sh ps - 8)
  with (Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) - Z.of_nat (length (pc_buf (PbCut sh ps None))) - 16)
  by (unfold rs_at_of, rs_plen; lia).
unfold has_params, params_struct, pc_ents. cbn [p_props pc_props pc_open]. rewrite first_params_app.
destruct (Z.eqb_spec (rs_first ps) 1) as [E|E].
- rewrite (w5_first1 ps E). cbn [fst snd]. rewrite Z.eqb_refl. reflexivity.
- destruct (w5_first0 ps E) as [v Hv]. rewrite Hv.
  destruct v; reflexivity.
Qed.
End i.

(* ======================================== the tactics of the pieces ======================================== *)
(* membership in a cut's (location, value) list, and a register outside a clobber list *)
Ltac w5_in := cbn [rs_Rc rs_Rc0 rs_Kc rs_cur2 rs_cur2s rs_L_KEY rs_L_pod rs_L_LATCH app In fst snd];
  repeat (first [left; reflexivity | right]).
Ltac w5_notin :=
let H := fresh "H" in intros H; cbn [In] in H;
repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]); exact H.
(* a location of the end cut that the piece kept: from the start cut's list Hat, its register outside the clobber
   list (Hkeep) or its 8 bytes in a range the piece did not write (Kc) *)
Ltac w5_kept Hat Hkeep Kc := lazymatch goal with |- rl_at _ _ _ _ _ ?l ?v =>
  apply (rm_at_kept rsegs _ _ _ _ _ _ _ l v (proj1 (Forall_forall _ _) Hat (l, v) ltac:(w5_in)));
  cbn [rm_keeps rl_xv];
  first [ apply Hkeep; [vm_compute; discriminate | w5_notin]
        | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; apply Kc; lia ] end.
