(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at a529a88a6181 (its lines 1-340 and
   674-687: the cut helpers and the tactics of the pieces, not the pieces) for reac-pw/fuzz_rate image A: the rl_
   vocabulary becomes rt_ (rt_at, rt_loc, rt_renv's q_ fields, rt_seg_pre, rt_inw), rm_ becomes rtm_; rate's image
   record (its 0x1e0-byte real frame, its write ranges hi_w1, its 56 frame shadow bytes); pa_E1_R names rate's R range
   [R+0x60, R+0x120) of hi_w1; pa_input_now takes the segment start's rt_fsh fact (rate's rt_seg_pre has none);
   pa_loop7 .. pa_wf7 and pa_nth_skipn / pa_suffix_step are role's model facts, here beside the helpers. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): the helpers the pieces of the property loop
   (lib/A/RtPgSeg.v rs_piece_W4_*_stmt) share. Proves no function (kind: segment lemma).

   HOW A PIECE USES THEM. Each piece runs its block lemma (the code from the cut's pc to its exits, in the shape of a
   callee contract, lib/A/RtPgSteps.v rts_post) from the facts the start cut holds, and then builds the end cut from
   the block's post: the journal and frame part (pa_core_step), the (location, value) facts (kept ones moved by
   pa_at_move, new ones from the block's relation), the frame's shadow, the first block's image (kept, or appended to
   by pa_pp_append through Layout.pp_image_put) and the model facts (Model.props_loop). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSteps RtPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgSeg RtPgPropKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* image A's loaded segments, as lib/A/RtPgSteps.v names them *)
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

(* ---- membership in a concrete location list (the cut lists of RtPgSeg.v are concatenations of definitions) ---- *)
Ltac pa_in :=
cbn [rs_Rc rs_Rc0 rs_Kc rs_Hc rs_cur2 rs_L_N rs_L_SEL rs_L_KEY rs_L_LATCH rs_L_P app In fst snd];
repeat (first [left; reflexivity | right]).
(* a register outside a concrete clobber list *)
Ltac pa_notin :=
let H := fresh "H" in intros H; cbn [In] in H;
repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]); exact H.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* ---- the (location, value) facts of a cut ---- *)
Lemma pa_at_get : forall H mem regs e L l v,
rs_at rsegs H mem regs e L -> In (l, v) L -> rt_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v HL Hin. unfold rs_at in HL. rewrite Forall_forall in HL. exact (HL (l, v) Hin). Qed.
Lemma pa_at_app : forall H mem regs e L1 L2,
rs_at rsegs H mem regs e L1 -> rs_at rsegs H mem regs e L2 -> rs_at rsegs H mem regs e (L1 ++ L2).
Proof. intros H mem regs e L1 L2 H1 H2. unfold rs_at in *. apply Forall_app. auto. Qed.
(* what a location needs to keep its value between two states *)
Definition pa_kept_loc (e : rt_renv) (regs regs' : bvmap 5 word) (H H' : word -> bool)
(mem mem' : word -> option byte) (l : rt_loc) : Prop :=
match l with
| LReg r => getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)
| LCell b o => forall j, 0 <= j < 8 -> aview rsegs H' mem' (rt_xv e b + o + j) = aview rsegs H mem (rt_xv e b + o + j)
end.
Lemma pa_at_move : forall H mem regs H' mem' regs' e L,
rs_at rsegs H mem regs e L -> Forall (fun f => pa_kept_loc e regs regs' H H' mem mem' (fst f)) L ->
rs_at rsegs H' mem' regs' e L.
Proof.
intros H mem regs H' mem' regs' e L HL HK. unfold rs_at in *.
induction L as [|[l v] L IH]; [constructor|].
inversion HL as [|? ? H1 H2]; subst. inversion HK as [|? ? K1 K2]; subst.
constructor; [|apply IH; assumption].
cbn [fst snd] in *. destruct l as [r|b o]; cbn [rt_at pa_kept_loc] in *.
- rewrite K1. exact H1.
- eapply val_mem_kept; [|exact H1]. intros j Hj. apply K1. lia.
Qed.

Lemma pa_aview_mod : forall H mem a, aview rsegs H mem a = aview rsegs H mem (a mod 2 ^ 64).
Proof. intros H mem a. unfold aview, mbyte. rewrite Z_to_bv_mod64. reflexivity. Qed.
(* a block that writes nothing keeps every byte, also outside [0, 2^64) *)
Lemma pa_mem_all : forall H mem H' mem',
(forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs H' mem' a = aview rsegs H mem a) ->
forall a, aview rsegs H' mem' a = aview rsegs H mem a.
Proof.
intros H mem H' mem' K a. rewrite (pa_aview_mod H' mem' a), (pa_aview_mod H mem a).
apply K; [apply Z.mod_pos_bound; lia | tauto].
Qed.

(* ---- the journal-and-frame part of a cut, after a block ---- *)
Lemma pa_core_step : forall cx E (Ew : Z -> Prop) ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rs_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly3 S3 W3 mem3 md3 (x_k cx) ->
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Ew a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
(forall a, Ew a -> (spZ (x_regs cx) - T_SEG_STK <= a < spZ (x_regs cx)) \/ E a) ->
rs_core rsegs B MT cx E ly3 S3 W3 regs3 mem3 md3.
Proof using MTL.
intros cx E Ew ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hc HJ3 Hr3 Hf3 Hp3 Hio3 Hmo3 Hm3 HEw.
unfold rs_core, rs_mid in *. destruct Hc as (HJ & Hr & Hf & Hp & Hio & Hmo & Hm).
split; [exact HJ3|].
split; [intros r Hr'; rewrite (Hr3 r Hr'); exact (Hr r Hr')|].
split; [rewrite Hf3; exact Hf|].
split; [eapply Permutation_trans; [exact Hp3 | exact Hp]|].
split; [eapply same_io_trans; [exact Hio | exact Hio3]|].
split; [replace 0 with (0 + 0) by reflexivity; exact (mle_station MT _ _ _ 0 0 MTL Hmo Hmo3)|].
intros a Ha Hs HE. rewrite <- (Hm a Ha Hs HE). apply Hm3; [exact Ha|].
intros HW. destruct (HEw a HW) as [X|X]; [exact (Hs X) | exact (HE X)].
Qed.

(* ---- the segment's write set: R's cells [R+0x60, R+0x120) (hi_w1's fourth range) and the first block ---- *)
Lemma pa_E1_R : forall cx a, q_R (x_e cx) + 0x60 <= a < q_R (x_e cx) + 0x120 -> rs_E1 rsegs cx a.
Proof.
intros cx a Ha. left. unfold rt_inw. cbn [hi_w1 rate_himg_A].
apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rt_xv]. lia.
Qed.
Lemma pa_E1_pp : forall cx a, q_pp (x_e cx) <= a < q_pp (x_e cx) + Layout.PP_SIZE -> rs_E1 rsegs cx a.
Proof. intros cx a Ha. right. exact Ha. Qed.

(* ---- the first block's image at a property cut: its bounds ---- *)
Lemma pa_img_bounds : forall sh ps, rs_wf sh ps -> (length ps <= 2)%nat ->
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

(* ---- pod_put into the first block (pod.h:175-182): x appended at len, len := len + |x|, every other byte kept
   [Layout.pp_image_put] ---- *)
Lemma pa_pp_append : forall H mem H' mem' pp b x isp hasp pst es corr,
Z.of_nat (length b + length x) <= Layout.POD_BUF_MAX -> (length es <= 32)%nat ->
Forall (fun e => (length (e_body e) <= 96)%nat) es ->
rtm_bytes rsegs H mem pp (pp_image b isp hasp pst es corr) ->
rtm_bytes rsegs H' mem' (pp + Z.of_nat (length b)) x ->
val_mem rsegs (mrestrict H' mem') (pp + Layout.OFF_LEN) 8 (Z.of_nat (length b + length x)) ->
(forall y, pp <= y < pp + Layout.PP_SIZE ->
 ~ (pp + Z.of_nat (length b) <= y < pp + Z.of_nat (length b) + Z.of_nat (length x)) ->
 ~ (pp + Layout.OFF_LEN <= y < pp + Layout.OFF_LEN + 8) -> aview rsegs H' mem' y = aview rsegs H mem y) ->
rtm_bytes rsegs H' mem' pp (pp_image (b ++ x) isp hasp pst es corr).
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
apply rtm_bytes_app in Old as [Ob Old]. rewrite <- app_assoc in Old.
apply rtm_bytes_app in Old as [_ Old]. apply rtm_bytes_app in Old as [Ozk Old].
apply rtm_bytes_app in Old as [_ OT].
rewrite length_zeros in Ozk, OT. rewrite length_zeros, length_le64 in OT.
rewrite <- app_assoc. apply rtm_bytes_app. split.
{ eapply (rtm_bytes_kept rsegs); [exact Ob|]. intros y Hy. apply K; unfold Layout.PP_SIZE, Layout.OFF_LEN in *; lia. }
apply rtm_bytes_app. split; [exact Nx|].
apply rtm_bytes_app. split.
{ eapply (rtm_bytes_kept rsegs); [exact Ozk|]. intros y Hy. rewrite length_zeros in Hy.
  apply K; unfold Layout.PP_SIZE, Layout.OFF_LEN in *; lia. }
rewrite length_zeros. apply rtm_bytes_app. split.
{ unfold le64. apply rtm_bytes_of_val.
  replace (pp + Z.of_nat (length b) + Z.of_nat (length x) + Z.of_nat k) with (pp + Layout.OFF_LEN)
    by (unfold Layout.OFF_LEN; lia).
  rewrite length_app. exact Nlen. }
rewrite length_le64. eapply (rtm_bytes_kept rsegs).
- replace (pp + Z.of_nat (length b) + Z.of_nat (length x) + Z.of_nat k + Z.of_nat 8)
    with (pp + Z.of_nat (length b) + Z.of_nat (length x) + Z.of_nat k + 8) by lia. exact OT.
- intros y Hy. apply K; unfold Layout.PP_SIZE, Layout.OFF_LEN in *; lia.
Qed.

(* ---- the first block at the segment's start: live, made since the journal's start, in application memory ---- *)
Lemma pa_pp_blocks : forall cx, rs_pre rsegs B cx ->
In (q_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_lyc cx) (x_Sc cx)) /\
~ In (q_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_ly cx) (x_S cx)) /\
amem_range (q_pp (x_e cx)) Layout.PP_SIZE.
Proof using LAWS.
intros cx Hpre. unfold rs_pre, rt_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & HR16 & HRs & HRstk & Hown & HF & Hpp0 & Hpp & Hhdr & Hro &
  Hglobs & Hrz & Hstrs & Hcells & Hrom & Hout & Hi32 & Hu64).
split; [exact Hpp|]. split; [exact Hout|].
eapply (amem_range_of_block rsegs B LAWS); [exact (proj1 HJ) | exact Hpp | lia | reflexivity].
Qed.

(* ---- the model of one shape-7 property (Model.prop_step's first arm) ---- *)
Lemma pa_loop7 : forall n inp, props_loop 7 (S n) inp =
(fst (props_loop 7 n inp) ++ [(0, PInt 0)], snd (fuzz_u8 (snd (props_loop 7 n inp)))).
Proof.
intros n inp. rewrite props_loop_S_end. destruct (props_loop 7 n inp) as [ps0 r0]. cbn [fst snd].
unfold prop_step. destruct (fuzz_u8 r0) as [sel r1]. reflexivity.
Qed.
Lemma pa_seen7 : forall ps, rs_seen (ps ++ [(0, PInt 0)]) = rs_seen ps.
Proof. intros ps. unfold rs_seen. rewrite existsb_app. cbn. rewrite orb_false_r. reflexivity. Qed.
Lemma pa_img7 : forall ps, pc_image (PbCut 7 (ps ++ [(0, PInt 0)]) None) =
pp_image (pc_buf (PbCut 7 ps None) ++ prop_bytes 7 (0, PInt 0)) (is_props (PodRec 7 ps None))
  (has_params (PodRec 7 ps None)) (params_struct (PodRec 7 ps None)) (pc_ents (PbCut 7 ps None)) false.
Proof.
intros ps. unfold pc_image. cbn [pc_shape pc_props pc_open]. rewrite <- pc_buf_prop.
unfold has_params, params_struct, pc_ents. cbn [p_props pc_props pc_open]. rewrite first_params_app.
destruct (first_params ps); reflexivity.
Qed.
Lemma pa_wf7 : forall ps, rs_wf 7 ps -> (length ps <= 2)%nat -> rs_wf 7 (ps ++ [(0, PInt 0)]).
Proof.
intros ps (Hs & Hk & He & Hl) H2. split; [exact Hs|]. split.
- apply Forall_app. split; [exact Hk|]. constructor; [cbn; split; [lia | exact I] | constructor].
- split; [unfold all_ents in *; rewrite flat_map_app; cbn; rewrite app_nil_r; exact He|].
  rewrite length_app. cbn. lia.
Qed.

(* ---- facts every piece takes from the segment's start ---- *)
Lemma pa_R_bounds : forall cx, rs_pre rsegs B cx ->
let e := x_e cx in
x_sp0 cx - x_STK cx + T_SEG_STK <= q_R e /\ q_R e + 0x1e0 <= x_sp0 cx /\ q_R e mod 16 = 0 /\
2 ^ 46 <= q_R e /\ x_sp0 cx <= 2 ^ 47 /\ getr (x_regs cx) 2 = w64 (q_R e) /\ alloc_ceiling + T_SEG_STK <= q_R e.
Proof.
intros cx Hpre e. unfold rs_pre, rt_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & HR16 & HRs & HRstk & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HST0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _). cbn [hi_rsz rate_himg_A] in HRs. subst e.
unfold T_SEG_STK, ASTACK in *. repeat split; try lia. exact H2.
Qed.
Lemma pa_blk_bounds : forall cx, rs_pre rsegs B cx ->
let e := x_e cx in
4096 <= q_pp e /\ q_pp e + Layout.PP_SIZE <= alloc_ceiling /\
4096 <= q_F e /\ q_F e + 512 <= alloc_ceiling /\ in_app (q_F e) 512.
Proof using LAWS.
intros cx Hpre e. unfold rs_pre, rt_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & HR16 & HRs & HRstk & Hown & HF & Hpp0 & Hpp & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hpp) as (_ & Hp4096 & Hpceil & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Hpceil.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (hi_cid rate_himg_A, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HAR Hin) as (F1 & F2 & F3).
rewrite <- HF in F1, F2, F3. cbn [hi_cid rate_himg_A] in F2, F3. change (fs_frame_bytes 3) with 512 in F2, F3.
subst e. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact F3].
Qed.

(* ---- the input at a cut of the build: its bytes and their shadow as at the segment's start (rs_in) ---- *)
Lemma pa_input_now : forall cx rest ly2 S2 W2 regs2 mem2 md2 c,
rs_pre rsegs B cx -> rt_fsh rsegs (w_H (x_W cx)) (x_memc cx) (q_F (x_e cx)) (hi_shA rate_himg_A) ->
rs_in rsegs cx rest -> rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
rs_fsh_at rsegs cx W2 mem2 rs_P0 -> 0 <= c < Z.of_nat (length rest) ->
val_mem rsegs (mrestrict (w_H W2) mem2) (q_src (x_e cx) + c) 1 (nth (Z.to_nat c) (rs_u8s rest) 0) /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (q_src (x_e cx) + c) 1.
Proof using LAWS.
intros cx rest ly2 S2 W2 regs2 mem2 md2 c Hpre Hfsh0 Hin Hcore Hfsh Hc.
pose proof (pa_R_bounds cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
pose proof (pa_blk_bounds cx Hpre) as (PB1 & PB2 & FB1 & FB2 & FB3).
pose proof (pa_pp_blocks cx Hpre) as (_ & _ & PA).
assert (PA' : q_pp (x_e cx) + Layout.PP_SIZE <= 0x7fff7fff \/ 0x10007fff8000 <= q_pp (x_e cx))
  by (destruct PA as [A|[A _]]; [left; exact A | right; exact A]). clear PA.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hin as (Hleft & Hgarr & Hra & Hhull & Hamr & Hsrc0 & Hsrcn & Hapart).
destruct Hcore as (_ & _ & _ & _ & _ & _ & Hkm).
assert (SP : spZ (x_regs cx) = q_R (x_e cx)) by (unfold spZ; rewrite RB6; unfold w64; apply unsigned_lit_small; lia).
rewrite SP in Hkm.
set (src := q_src (x_e cx)) in *.
(* the byte *)
assert (Ka : forall a, src <= a < src + q_left (x_e cx) ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).
{ intros a Ha. destruct (Hapart a Ha) as (N1 & N2 & N3). apply Hkm; [lia | exact N1 |].
  intros [X|X]; [exact (N2 X) | exact (N3 X)]. }
split.
- destruct (Hgarr (Z.to_nat c) ltac:(unfold rs_u8s; rewrite length_map; lia)) as [V _]. rewrite Z2Nat.id in V by lia.
  eapply val_mem_kept; [|exact V]. intros k Hk. apply Ka. lia.
- pose proof (rtm_in_ra _ _ _ _ c Hra ltac:(lia)) as R1. fold src in R1.
  intros y Hy. destruct (R1 y Hy) as (sv & Hs & Hok). exists sv. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr.
  assert (Y8 : 0 <= y / 8 < 2 ^ 44) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr;
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  set (sa := SHADOW_OFF + y / 8).
  destruct (Z_lt_le_dec sa (shadow_addr (q_F (x_e cx)))) as [Lo|Lo];
  [| destruct (Z_lt_le_dec sa (shadow_addr (q_F (x_e cx)) + 56)) as [Hi|Hi]].
  2:{ unfold rs_fsh_at, rt_fsh in Hfsh, Hfsh0. cbn [hi_shA rate_himg_A] in Hfsh0.
      replace sa with (shadow_addr (q_F (x_e cx)) + (sa - shadow_addr (q_F (x_e cx)))) by lia.
      rewrite (Hfsh (sa - shadow_addr (q_F (x_e cx))) ltac:(replace (Z.of_nat (length rs_P0)) with 56 by reflexivity; lia)).
      rewrite (Hfsh0 (sa - shadow_addr (q_F (x_e cx))) ltac:(replace (Z.of_nat (length rate_A_shA)) with 56 by reflexivity; lia)).
      reflexivity. }
  all: apply Hkm; [unfold sa, SHADOW_OFF; lia | unfold sa, SHADOW_OFF, T_SEG_STK, ASTACK in *; lia |].
  all: intros [X|X]; [unfold rt_inw in X; cbn [hi_w1 rate_himg_A] in X;
       repeat (apply Exists_cons in X as [X|X]; [cbn [fst snd rt_xv] in X|]); [..|apply Exists_nil in X; exact X] | ].
  all: unfold sa, shadow_addr, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, amem_range, kLowMemEnd, kHighMemEnd, Layout.PP_SIZE in *; lia.
Qed.

End g.

(* ---- the input's cursor after one byte read ---- *)
Lemma pa_nth_skipn : forall (l : list byte) j bb r, skipn j l = bb :: r ->
(j < length l)%nat /\ nth j l (Z_to_bv 8 0) = bb.
Proof.
induction l as [|x l IH]; intros j bb r H; destruct j as [|j]; cbn [skipn length nth] in *; try discriminate.
- injection H as <- <-. split; [lia | reflexivity].
- destruct (IH j bb r H) as [H1 H2]. split; [lia | exact H2].
Qed.
Lemma pa_suffix_step : forall rest r, rs_suffix rest r -> rs_suffix rest (snd (fuzz_u8 r)).
Proof.
intros rest r (j & Hj & ->). destruct (skipn j rest) as [|bb r'] eqn:E; cbn [fuzz_u8 snd].
- exists j. split; [exact Hj | symmetry; exact E].
- destruct (pa_nth_skipn rest j bb r' E) as [Hjl _]. exists (S j). split; [lia|].
  replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, E. reflexivity.
Qed.

(* ---- the tactics of the pieces ---- *)
Ltac pa_take Hat l v H := pose proof (pa_at_get _ _ _ _ _ l v Hat ltac:(pa_in)) as H; cbn [rt_at rt_xv] in H.
Ltac pa_from Hat := lazymatch goal with |- rt_at _ _ _ _ _ ?l ?v => exact (pa_at_get _ _ _ _ _ l v Hat ltac:(pa_in)) end.
Ltac pa_list := unfold rs_at_cx, rs_at;
cbn [rs_L_N rs_L_SEL rs_L_KEY rs_L_LATCH rs_L_P rs_Rc rs_Rc0 rs_Kc rs_Hc rs_cur2 app];
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
(* every location of a list keeps its value: registers outside clob (Hkeep), cells outside the write set *)
Ltac pa_kept Hkeep celltac :=
cbn [rs_L_N rs_L_SEL rs_L_KEY rs_L_LATCH rs_L_P rs_Rc rs_Rc0 rs_Kc rs_Hc rs_cur2 app];
repeat apply Forall_cons; try apply Forall_nil; cbn [fst pa_kept_loc rt_xv];
first [ apply Hkeep; [cbv; discriminate | pa_notin]
      | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; celltac ].
Ltac pa_regs234 Hkeep := let r := fresh "r" in intros r [-> | [-> | ->]]; (apply Hkeep; [cbv; discriminate | pa_notin]).

Print Assumptions pa_input_now.
Print Assumptions pa_pp_append.
