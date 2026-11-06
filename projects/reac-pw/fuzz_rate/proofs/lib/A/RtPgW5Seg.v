(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Seg.v at dae3dba91f37 for reac-pw/fuzz_rate's
   image A: module paths changed; the cut vocabulary is rate's (lib/A/RtPgSeg.v, rt_ / q_ names); the segment's start
   is rate's rt_seg_pre (real frame 0x1e0 bytes) and the read-only image at a cut (w5_rom_now) is added. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a): the bridge between the cut states of
   lib/A/RtPgSeg.v and the core lemmas of the W5 pieces (lib/A/RtPgW5Close.v and its two siblings), whose start and
   end are stated as explicit register, cell and byte facts with a w5_post (lib/A/RtPgW5Kit.v). Proves no function
   (kind: segment lemma).
   - w5_getr5: a register named by Z_to_bv 5 r (rt_at's form) is the register named by the literal.
   - w5_at_reg / w5_at_cell: a fact of a cut's (location, value) list, read back.
   - w5_core_post: a cut's segment frame (rs_core) is carried across a piece's w5_post whose write set lies in
     the segment's.
   - w5_pre_facts: what the segment's start fixes of the real frame, the frame for locals and the first block.
   - w5_rom_now: the read-only image bytes at a cut inside the build are the image's (the segment's rom_view, kept by
     rs_core: no read-only byte lies in the callees' stack, the frame for locals, its shadow, the real frame or pp).
   - the first block's image: w5_img_buf / w5_img_flags / w5_img_gen (an image rebuilt from its parts) and
     w5_img_close_eq (the image at the Struct's close). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgMem RtPgSeg RtPgW5Kit.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* image A's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

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
rtm_bytes rsegs H mem a l -> length l' = length l ->
(forall j, (j < length l)%nat -> Pb (a + Z.of_nat j) = false ->
  aview rsegs H' mem' (a + Z.of_nat j) = aview rsegs H mem (a + Z.of_nat j) /\
  nth j l' (Z_to_bv 8 0) = nth j l (Z_to_bv 8 0)) ->
(forall j, (j < length l)%nat -> Pb (a + Z.of_nat j) = true ->
  aview rsegs H' mem' (a + Z.of_nat j) = Some (bv_unsigned (nth j l' (Z_to_bv 8 0)))) ->
rtm_bytes rsegs H' mem' a l'.
Proof.
intros H mem H' mem' a l l' Pb Hb Hlen Hout Hin. apply rtm_bytes_aview. intros j Hj. rewrite Hlen in Hj.
destruct (Pb (a + Z.of_nat j)) eqn:E; [exact (Hin j Hj E)|].
destruct (Hout j Hj E) as [A N]. rewrite A, N. exact (proj1 (rtm_bytes_aview rsegs H mem a l) Hb j Hj).
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

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

Lemma w5_at_reg : forall H mem regs e (L : list (rt_loc * Z)) r v,
rs_at rsegs H mem regs e L -> In (LReg r, v) L -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros H mem regs e L r v HL Hin. exact (proj1 (Forall_forall _ _) HL _ Hin). Qed.
Lemma w5_at_cell : forall H mem regs e (L : list (rt_loc * Z)) o v,
rs_at rsegs H mem regs e L -> In (LCell XR o, v) L ->
val_mem rsegs (mrestrict H mem) (q_R e + o) 8 (v mod 2 ^ 64).
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
(* the real frame, the frame for locals and the first block, as the segment's start fixes them *)
Lemma w5_pre_facts : forall cx, rs_pre rsegs B cx ->
  x_sp0 cx - x_STK cx <= q_R (x_e cx) - T_SEG_STK /\ q_R (x_e cx) + 0x1e0 <= x_sp0 cx /\
  q_R (x_e cx) mod 16 = 0 /\ getr (x_regs cx) 2 = w64 (q_R (x_e cx)) /\
  alloc_ceiling + T_SEG_STK <= q_R (x_e cx) /\ x_sp0 cx <= 2 ^ 47 /\
  In (q_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_lyc cx) (x_Sc cx)) /\
  ~ In (q_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_ly cx) (x_S cx)) /\
  4096 <= q_pp (x_e cx) /\ q_pp (x_e cx) + Layout.PP_SIZE <= alloc_ceiling /\
  4096 <= q_F (x_e cx) /\ q_F (x_e cx) + 512 <= alloc_ceiling /\ in_app (q_pp (x_e cx)) Layout.PP_SIZE.
Proof using LAWS.
intros cx Hpre. unfold rs_pre, rt_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & HR16 & HRs & HRstk & Hown & HF & Hpp0 & Hpp & Hhdr & Hro &
  Hglobs & Hrz & Hstrs & Hcells & Hrom & Hout & Hi32 & Hu64).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HST0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp) as (_ & Hp4096 & Hpceil & Happ & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Hpceil, Happ.
assert (Hin : In (hi_cid rate_himg_A, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HAR Hin) as (F1 & F2 & _).
rewrite <- HF in F1, F2. cbn [hi_cid rate_himg_A] in F2. change (fs_frame_bytes 3) with 512 in F2.
pose proof asan_consts as (C1 & _). cbn [hi_rsz rate_himg_A] in HRs.
unfold T_SEG_STK, ASTACK in *.
split; [lia|]. split; [lia|]. split; [exact HR16|]. split; [exact H2|]. split; [lia|]. split; [lia|].
split; [exact Hpp|]. split; [exact Hout|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. exact Happ.
Qed.

(* the read-only image at a cut of the build: the segment's rom_view, kept by rs_core *)
Lemma w5_rom_now : forall cx ly2 S2 W2 regs2 mem2 md2,
  rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
  rom_view rsegs W2 mem2.
Proof using LAWS.
intros cx ly2 S2 W2 regs2 mem2 md2 Hpre Hcore.
pose proof (w5_pre_facts cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & Ppin & Ppout & PB1 & PB2 & FB1 & FB2 & PApp).
pose proof Hpre as Hpre'. unfold rs_pre, rt_seg_pre in Hpre'.
destruct Hpre' as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & HF & _ & _ & _ & _ & _ & _ & _ & _ & Hrom & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (hi_cid rate_himg_A, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct Hcore as (_ & _ & _ & _ & _ & _ & Hmem).
pose proof ASAN_CEIL_range as ([AC1 AC2] & _). unfold ASAN_CEIL in AC1, AC2.
assert (HTS : T_SEG_STK = 16384) by reflexivity.
intros a Ha. pose proof Ha as (sg & Hsg & _ & Hr).
assert (Himg : in_img rsegs a) by (exists sg; split; [exact Hsg | exact Hr]).
pose proof (w5_segs_low a Himg) as Hlow.
assert (Hsp : spZ (x_regs cx) = q_R (x_e cx)) by (unfold spZ; rewrite RB4; unfold w64; apply unsigned_lit_small; lia).
unfold kLowMemEnd in Hlow.
rewrite (Hmem a); [exact (Hrom a Ha) | lia | rewrite Hsp; unfold T_SEG_STK, ASTACK in *; lia |].
(* a read-only byte is no byte of the segment's write set: pp and the frame for locals are client memory, which no
   image byte is (AR_client_img_law); the frame's shadow and the real frame lie above the image *)
intros [Hw | Hp].
- unfold rt_inw in Hw. cbn [hi_w1 rate_himg_A] in Hw.
  apply Exists_cons in Hw as [Hw | Hw]; cbn [fst snd rt_xv] in Hw.
  { (* the frame for locals F + 0x20 .. F + 0x158 *)
    assert (Hc : exists cid pos, In (cid, pos) (frames (x_Sc cx)) /\
      frame_addr (x_lyc cx) cid pos <= a < frame_addr (x_lyc cx) cid pos + fs_frame_bytes cid).
    { exists (hi_cid rate_himg_A), (x_pos cx). split; [exact Hin|].
      rewrite <- HF. cbn [hi_cid rate_himg_A]. change (fs_frame_bytes 3) with 512. lia. }
    destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR (or_intror (or_introl Hc))) as [_ Hni].
    exact (Hni Himg). }
  apply Exists_cons in Hw as [Hw | Hw]; cbn [fst snd rt_xv] in Hw.
  { unfold shadow_addr, SHADOW_OFF in Hw. pose proof (Z.div_pos (q_F (x_e cx)) 8 ltac:(lia)). lia. }
  repeat (apply Exists_cons in Hw as [Hw | Hw];
    [cbn [fst snd rt_xv] in Hw; unfold T_SEG_STK, ASTACK in *; lia |]).
  apply Exists_nil in Hw. exact Hw.
- assert (Hc : exists p n, In (p, n) (ablocks B (x_lyc cx) (x_Sc cx)) /\ p <= a < p + req_size n).
  { exists (q_pp (x_e cx)), Layout.PP_SIZE. split; [exact Ppin|]. change (req_size Layout.PP_SIZE) with 19744.
    unfold Layout.PP_SIZE in Hp. lia. }
  destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR (or_introl Hc)) as [_ Hni].
  exact (Hni Himg).
Qed.
End s.

(* ======================================== the first block's image ======================================== *)
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* buf[0..len) of an image *)
Lemma w5_img_buf : forall H mem pp b isp hp pst es corr,
rtm_bytes rsegs H mem pp (pp_image b isp hp pst es corr) -> rtm_bytes rsegs H mem pp b.
Proof. intros H mem pp b isp hp pst es corr Hb. rewrite pp_image_tail in Hb. apply rtm_bytes_app in Hb as [Hb _]. exact Hb. Qed.
(* the two flag words of an image, carried to a state that keeps them *)
Lemma w5_img_flags : forall H mem H' mem' pp b isp hp pst es corr,
Z.of_nat (length b) <= POD_BUF_MAX -> (length es <= 32)%nat -> Forall (fun e => (length (e_body e) <= 96)%nat) es ->
rtm_bytes rsegs H mem pp (pp_image b isp hp pst es corr) ->
(forall y, pp + OFF_HAS_PARAMS <= y < pp + OFF_ENT -> aview rsegs H' mem' y = aview rsegs H mem y) ->
rtm_bytes rsegs H' mem' (pp + OFF_HAS_PARAMS) (le32 (Z.b2z hp)) /\
rtm_bytes rsegs H' mem' (pp + OFF_PARAMS_STRUCT) (le32 (Z.b2z pst)).
Proof.
intros H mem H' mem' pp b isp hp pst es corr Hb He Hs Old K.
pose proof (rtm_pp_has_params rsegs b isp hp pst es corr Hb He Hs H mem pp Old) as V1.
pose proof (rtm_pp_params_struct rsegs b isp hp pst es corr Hb He Hs H mem pp Old) as V2.
split; (eapply rtm_bytes_kept; [apply rtm_bytes_of_val; eassumption|]);
  intros y Hy; rewrite ?length_le32, ?length_Z_to_le_bytes in Hy; apply K; unfold OFF_HAS_PARAMS, OFF_PARAMS_STRUCT, OFF_ENT in *; lia.
Qed.
(* an image rebuilt from its parts: buf[0..len) grown or patched (b'), len, the two flag words, every other byte
   kept from the old image (the zeros after b', is_props, the entries and what follows them) *)
Lemma w5_img_gen : forall H mem H' mem' pp b b' isp hp pst hp' pst' es corr,
(length b <= length b')%nat -> Z.of_nat (length b') <= POD_BUF_MAX -> (length es <= 32)%nat ->
Forall (fun e => (length (e_body e) <= 96)%nat) es ->
rtm_bytes rsegs H mem pp (pp_image b isp hp pst es corr) ->
rtm_bytes rsegs H' mem' pp b' ->
val_mem rsegs (mrestrict H' mem') (pp + OFF_LEN) 8 (Z.of_nat (length b')) ->
rtm_bytes rsegs H' mem' (pp + OFF_HAS_PARAMS) (le32 (Z.b2z hp')) ->
rtm_bytes rsegs H' mem' (pp + OFF_PARAMS_STRUCT) (le32 (Z.b2z pst')) ->
(forall y, pp + Z.of_nat (length b') <= y < pp + OFF_LEN \/ pp + OFF_IS_PROPS <= y < pp + OFF_HAS_PARAMS \/
  pp + OFF_ENT <= y < pp + PP_SIZE -> aview rsegs H' mem' y = aview rsegs H mem y) ->
rtm_bytes rsegs H' mem' pp (pp_image b' isp hp' pst' es corr).
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
apply rtm_bytes_app in Old as [_ Old]. apply rtm_bytes_app in Old as [_ Old].
apply rtm_bytes_app in Old as [Ozk Old]. apply rtm_bytes_app in Old as [_ Old].
apply rtm_bytes_app in Old as [Oi Old]. apply rtm_bytes_app in Old as [_ Old].
apply rtm_bytes_app in Old as [_ OT].
repeat (first [rewrite length_zeros in Ozk | rewrite length_zeros in Oi | rewrite length_zeros in OT |
  rewrite length_le64 in Oi | rewrite length_le64 in OT | rewrite length_le32 in OT]).
apply rtm_bytes_app. split; [exact Nb|].
apply rtm_bytes_app. split.
{ eapply rtm_bytes_kept.
  - replace (pp + Z.of_nat (length b')) with (pp + Z.of_nat (length b) + Z.of_nat (length b' - length b)) by lia.
    exact Ozk.
  - intros y Hy. rewrite length_zeros in Hy. apply K. left. unfold OFF_LEN. lia. }
rewrite length_zeros.
apply rtm_bytes_app. split.
{ unfold le64. apply rtm_bytes_of_val.
  replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b')))) with (pp + OFF_LEN)
    by (unfold OFF_LEN; lia). exact Nlen. }
rewrite length_le64.
apply rtm_bytes_app. split.
{ eapply rtm_bytes_kept.
  - replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8)
      with (pp + Z.of_nat (length b) + Z.of_nat (length b' - length b) +
            Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8) by lia.
    exact Oi.
  - intros y Hy. rewrite length_le32 in Hy. apply K. right. left. unfold OFF_IS_PROPS, OFF_HAS_PARAMS. lia. }
rewrite length_le32.
apply rtm_bytes_app. split.
{ replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8 + Z.of_nat 4)
    with (pp + OFF_HAS_PARAMS) by (unfold OFF_HAS_PARAMS; lia). exact Nh. }
rewrite length_le32.
apply rtm_bytes_app. split.
{ replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8 + Z.of_nat 4
    + Z.of_nat 4) with (pp + OFF_PARAMS_STRUCT) by (unfold OFF_PARAMS_STRUCT; lia). exact Np. }
rewrite length_le32.
eapply rtm_bytes_kept.
- replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8 + Z.of_nat 4
    + Z.of_nat 4 + Z.of_nat 4)
    with (pp + Z.of_nat (length b) + Z.of_nat (length b' - length b) +
          Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4) by lia.
  exact OT.
- intros y Hy. apply K. right. right. unfold OFF_ENT. lia.
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
