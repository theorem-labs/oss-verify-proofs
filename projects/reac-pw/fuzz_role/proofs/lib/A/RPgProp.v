(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address below is measured on its unstripped
   twin sha256 6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6): the four pieces of one turn of the
   property loop of LLVMFuzzerTestOneInput (0x7ff88) as lib/A/RPgSeg.v states them (rs_piece_W4_sel_stmt,
   rs_piece_W4_int7_stmt, rs_piece_W4_key_stmt, rs_piece_W4_latch_stmt). Proves no function (kind: segment lemma).

   HOW. Each piece runs its block lemma (lib/A/RPgPropSel.v, RPgPropSelB.v, RPgPropIntB.v, RPgPropKeyB.v: the code
   from the cut's pc to its exits, in the shape of a callee contract) from the facts the start cut holds, and then
   builds the end cut from the block's post: the journal and frame part (pa_core_step), the (location, value) facts
   (kept ones moved by pa_at_move, new ones from the block's relation), the frame's shadow, the first block's image
   (kept, or appended to by pa_pp_append through Layout.pp_image_put) and the model facts (Model.props_loop). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgSteps RPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgSeg RPgPropKit RPgPropSel RPgPropSelB RPgPropIntB RPgPropKeyB.
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

(* ---- membership in a concrete location list (the cut lists of RPgSeg.v are concatenations of definitions) ---- *)
Ltac pa_in :=
cbn [rs_Rc rs_Rc0 rs_Kc rs_cur2 rs_L_N rs_L_SEL rs_L_KEY rs_L_P app In fst snd];
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
rs_at rsegs H mem regs e L -> In (l, v) L -> rl_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v HL Hin. unfold rs_at in HL. rewrite Forall_forall in HL. exact (HL (l, v) Hin). Qed.
Lemma pa_at_app : forall H mem regs e L1 L2,
rs_at rsegs H mem regs e L1 -> rs_at rsegs H mem regs e L2 -> rs_at rsegs H mem regs e (L1 ++ L2).
Proof. intros H mem regs e L1 L2 H1 H2. unfold rs_at in *. apply Forall_app. auto. Qed.
(* what a location needs to keep its value between two states *)
Definition pa_kept_loc (e : rl_env) (regs regs' : bvmap 5 word) (H H' : word -> bool)
(mem mem' : word -> option byte) (l : rl_loc) : Prop :=
match l with
| LReg r => getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)
| LCell b o => forall j, 0 <= j < 8 -> aview rsegs H' mem' (rl_xv e b + o + j) = aview rsegs H mem (rl_xv e b + o + j)
end.
Lemma pa_at_move : forall H mem regs H' mem' regs' e L,
rs_at rsegs H mem regs e L -> Forall (fun f => pa_kept_loc e regs regs' H H' mem mem' (fst f)) L ->
rs_at rsegs H' mem' regs' e L.
Proof.
intros H mem regs H' mem' regs' e L HL HK. unfold rs_at in *.
induction L as [|[l v] L IH]; [constructor|].
inversion HL as [|? ? H1 H2]; subst. inversion HK as [|? ? K1 K2]; subst.
constructor; [|apply IH; assumption].
cbn [fst snd] in *. destruct l as [r|b o]; cbn [rl_at pa_kept_loc] in *.
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


(* ---- the segment's write set ---- *)
Lemma pa_E1_R : forall cx a, e_R (x_e cx) <= a < e_R (x_e cx) + 0x138 -> rs_E1 rsegs cx a.
Proof.
intros cx a Ha. left. unfold rl_inw. cbn [hi_w1 role_himg_A].
apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rl_xv]. lia.
Qed.
Lemma pa_E1_pp : forall cx a, e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE -> rs_E1 rsegs cx a.
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


(* ---- the first block at the segment's start: live, made since the journal's start, in application memory ---- *)
Lemma pa_pp_blocks : forall cx, rs_pre rsegs B cx ->
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
x_sp0 cx - x_STK cx + T_SEG_STK <= e_R e /\ e_R e + 0x1a0 <= x_sp0 cx /\ e_R e mod 16 = 0 /\
2 ^ 46 <= e_R e /\ x_sp0 cx <= 2 ^ 47 /\ getr (x_regs cx) 2 = w64 (e_R e) /\ alloc_ceiling + T_SEG_STK <= e_R e.
Proof.
intros cx Hpre e. unfold rs_pre, rl_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & HR16 & HRs & HRstk & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HST0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _). cbn [hi_rsz role_himg_A] in HRs. subst e.
unfold T_SEG_STK, ASTACK in *. repeat split; try lia. exact H2.
Qed.
Lemma pa_blk_bounds : forall cx, rs_pre rsegs B cx ->
let e := x_e cx in
4096 <= e_pp e /\ e_pp e + Layout.PP_SIZE <= alloc_ceiling /\
4096 <= e_F e /\ e_F e + 512 <= alloc_ceiling /\ in_app (e_F e) 512.
Proof using LAWS.
intros cx Hpre e. unfold rs_pre, rl_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & HR16 & HRs & HRstk & Hown & HF & Hfsh & Hpp0 & Hpp & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hpp) as (_ & Hp4096 & Hpceil & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Hpceil.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (hi_cid role_himg_A, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HAR Hin) as (F1 & F2 & F3).
rewrite <- HF in F1, F2, F3. cbn [hi_cid role_himg_A] in F2, F3. change (fs_frame_bytes 3) with 512 in F2, F3.
subst e. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact F3].
Qed.

(* ---- the input at a cut of the build: its bytes and their shadow as at the segment's start (rs_in) ---- *)
Lemma pa_input_now : forall cx rest ly2 S2 W2 regs2 mem2 md2 c,
rs_pre rsegs B cx -> rs_in rsegs cx rest -> rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
rs_fsh_at rsegs cx W2 mem2 rs_P0 -> 0 <= c < Z.of_nat (length rest) ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_src (x_e cx) + c) 1 (nth (Z.to_nat c) (rs_u8s rest) 0) /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (e_src (x_e cx) + c) 1.
Proof using LAWS.
intros cx rest ly2 S2 W2 regs2 mem2 md2 c Hpre Hin Hcore Hfsh Hc.
pose proof (pa_R_bounds cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
pose proof (pa_blk_bounds cx Hpre) as (PB1 & PB2 & FB1 & FB2 & FB3).
pose proof (pa_pp_blocks cx Hpre) as (_ & _ & PA).
assert (PA' : e_pp (x_e cx) + Layout.PP_SIZE <= 0x7fff7fff \/ 0x10007fff8000 <= e_pp (x_e cx))
  by (destruct PA as [A|[A _]]; [left; exact A | right; exact A]). clear PA.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hpre as Hpre'. unfold rs_pre, rl_seg_pre in Hpre'.
destruct Hpre' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfsh0 & _).
destruct Hin as (Hleft & Hgarr & Hra & Hhull & Hamr & Hsrc0 & Hsrcn & Hapart).
destruct Hcore as (_ & _ & _ & _ & _ & _ & Hkm).
assert (SP : spZ (x_regs cx) = e_R (x_e cx)) by (unfold spZ; rewrite RB6; unfold w64; apply unsigned_lit_small; lia).
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
  [| destruct (Z_lt_le_dec sa (shadow_addr (e_F (x_e cx)) + 52)) as [Hi|Hi]].
  2:{ unfold rs_fsh_at, rl_fsh in Hfsh, Hfsh0. cbn [hi_shA role_himg_A] in Hfsh0.
      replace sa with (shadow_addr (e_F (x_e cx)) + (sa - shadow_addr (e_F (x_e cx)))) by lia.
      rewrite (Hfsh (sa - shadow_addr (e_F (x_e cx))) ltac:(replace (Z.of_nat (length rs_P0)) with 52 by reflexivity; lia)).
      rewrite (Hfsh0 (sa - shadow_addr (e_F (x_e cx))) ltac:(replace (Z.of_nat (length role_A_shA)) with 52 by reflexivity; lia)).
      reflexivity. }
  all: apply Hkm; [unfold sa, SHADOW_OFF; lia | unfold sa, SHADOW_OFF, T_SEG_STK, ASTACK in *; lia |].
  all: intros [X|X]; [unfold rl_inw in X; cbn [hi_w1 role_himg_A] in X;
       repeat (apply Exists_cons in X as [X|X]; [cbn [fst snd rl_xv] in X|]); [..|apply Exists_nil in X; exact X] | ].
  all: unfold sa, shadow_addr, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, amem_range, kLowMemEnd, kHighMemEnd, Layout.PP_SIZE in *; lia.
Qed.

End g.

(* ---- the tactics of the pieces ---- *)
Ltac pa_take Hat l v H := pose proof (pa_at_get _ _ _ _ _ l v Hat ltac:(pa_in)) as H; cbn [rl_at rl_xv] in H.
Ltac pa_from Hat := lazymatch goal with |- rl_at _ _ _ _ _ ?l ?v => exact (pa_at_get _ _ _ _ _ l v Hat ltac:(pa_in)) end.
Ltac pa_list := unfold rs_at_cx, rs_at;
cbn [rs_L_N rs_L_SEL rs_L_KEY rs_L_P rs_Rc rs_Rc0 rs_Kc rs_cur2 app];
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
(* every location of a list keeps its value: registers outside clob (Hkeep), cells outside the write set *)
Ltac pa_kept Hkeep celltac :=
cbn [rs_L_N rs_L_SEL rs_L_KEY rs_L_P rs_Rc rs_Rc0 rs_Kc rs_cur2 app];
repeat apply Forall_cons; try apply Forall_nil; cbn [fst pa_kept_loc rl_xv];
first [ apply Hkeep; [cbv; discriminate | pa_notin]
      | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; celltac ].
Ltac pa_regs234 Hkeep := let r := fresh "r" in intros r [-> | [-> | ->]]; (apply Hkeep; [cbv; discriminate | pa_notin]).

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* ================================ the latch: LATCH / LATCH7 -> N / P1 ================================ *)
Lemma pa_piece_latch : rs_piece_W4_latch_stmt rsegs B MT.
Proof using MTL LAWS.
unfold rs_piece_W4_latch_stmt. intros cx POST rest i Hst HN HP1.
destruct Hst as (Hpre & Hc1 & Hlen0 & Hin0).
pose proof (pa_R_bounds B cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
pose proof asan_consts as (C1 & _).
split.
- unfold rs_from_LATCH. intros ly2 S2 W2 regs2 mem2 md2 sh np ps r Hlen Hcut.
  destruct Hcut as [Hb Hat]. pose proof Hb as (Hcore & Hfsh & Hpp & Hin & Hsuf & Hwf & Hsh & Hnp & Hps & Hnp3 & Hloop).
  unfold rs_at_cx in Hat.
  pa_take Hat (LReg 9) (e_R (x_e cx)) A9.
  pa_take Hat (LCell XR 0xb8) (Z.of_nat (length ps) - 1) Ai.
  pa_take Hat (LCell XR 0x88) (rs_seen ps) As.
  pa_take Hat (LCell XR 0x90) np An.
  assert (Hseen : 0 <= rs_seen ps <= 1) by (unfold rs_seen; destruct (existsb _ _); cbn; lia).
  rewrite Z.mod_small in Ai, As, An by lia.
  pose proof Hcore as (HJ & _).
  eapply SRr_bind.
  { refine (pa_latch B MT MTL LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (Z.of_nat (length ps) - 1) (rs_seen ps) np
      HJ A9 _ _ Ai As An _ _ _ Hseen); lia. }
  intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
  destruct HR as (R16 & R25 & R10).
  pose proof (pa_mem_all _ _ _ _ Hmem) as Hall.
  assert (Hat3 : rs_at rsegs (w_H W3) mem3 regs3 (x_e cx)
    (rs_Rc rsegs cx ++ rs_Kc rsegs cx sh np ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000));
     (LCell XR 0xb8, Z.of_nat (length ps) - 1); (LCell XR 0x88, rs_seen ps)] ++ rs_cur2 rsegs cx rest r)).
  { eapply pa_at_move; [exact Hat|]. pa_kept Hkeep ltac:(apply Hall). }
  assert (Hcore3 : rs_core rsegs B MT cx (rs_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3).
  { refine (pa_core_step B MT MTL cx _ (fun _ => False) _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 _ Hfr Hperm Hio Hmo Hmem _);
    [pa_regs234 Hkeep | intros a []]. }
  assert (Hfsh3 : rs_fsh_at rsegs cx W3 mem3 rs_P0).
  { unfold rs_fsh_at in *. eapply rm_fsh_kept; [exact Hfsh|]. intros j Hj. apply Hall. }
  assert (Hpp3 : rs_pp_at rsegs cx W3 mem3 (pc_image (PbCut sh ps None))).
  { unfold rs_pp_at in *. eapply (rm_bytes_kept rsegs); [exact Hpp|]. intros x Hx. apply Hall. }
  destruct (Z.eqb_spec (Z.of_nat (length ps) - 1 + 1) np) as [Heq|Hne].
  + replace (Z.of_nat (length ps) - 1 + 1 =? np) with true by (symmetry; apply Z.eqb_eq; exact Heq).
    change (mkCfg (mkst regs3 (w64 PA_P1) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_P1 regs3 mem3 md3).
    apply (HP1 ly3 S3 W3 regs3 mem3 md3 sh np ps r).
    split.
    * split; [exact Hcore3|]. split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Hsuf|].
      split; [exact Hwf|]. split; [exact Hlen0|]. split; [exact Hsh|]. split; [exact Hnp|]. split; [lia | exact Hloop].
    * pa_list; pa_from Hat3.
  + replace (Z.of_nat (length ps) - 1 + 1 =? np) with false by (symmetry; apply Z.eqb_neq; exact Hne).
    change (mkCfg (mkst regs3 (w64 PA_N) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_N regs3 mem3 md3).
    apply (HN ly3 S3 W3 regs3 mem3 md3 sh np ps r Hlen).
    split; [exact Hcore3|]. split.
    * pa_list; first [pa_from Hat3 | idtac].
      -- cbn [rl_at]. refine (eq_trans R16 _). f_equal. lia.
      -- cbn [rl_at]. exact R25.
    * split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Hsuf|]. split; [exact Hwf|].
      split; [exact Hsh|]. split; [exact Hnp|]. split; [lia|]. split; [exact Hnp3 | exact Hloop].
- unfold rs_from_LATCH7. intros ly2 S2 W2 regs2 mem2 md2 sh np ps r Hlen Hcut.
  destruct Hcut as [Hb Hat]. pose proof Hb as (Hcore & Hfsh & Hpp & Hin & Hsuf & Hwf & Hsh & Hnp & Hps & Hnp3 & Hloop).
  unfold rs_at_cx in Hat.
  pa_take Hat (LReg 9) (e_R (x_e cx)) A9.
  pa_take Hat (LReg 16) (Z.of_nat (length ps) - 1) A16.
  pa_take Hat (LCell XR 0x90) np An.
  rewrite Z.mod_small in An by lia.
  pose proof Hcore as (HJ & _).
  eapply SRr_bind.
  { refine (pa_latch7 B MT MTL LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (Z.of_nat (length ps) - 1) np
      HJ A9 A16 _ _ An _ _ _); lia. }
  intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
  destruct HR as (R16 & R10).
  pose proof (pa_mem_all _ _ _ _ Hmem) as Hall.
  assert (Hat3 : rs_at rsegs (w_H W3) mem3 regs3 (x_e cx)
    (rs_Rc rsegs cx ++ rs_Kc rsegs cx sh np ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000));
     (LReg 25, rs_seen ps)] ++ rs_cur2 rsegs cx rest r)).
  { assert (Hat' : rs_at rsegs (w_H W2) mem2 regs2 (x_e cx)
      (rs_Rc rsegs cx ++ rs_Kc rsegs cx sh np ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000));
       (LReg 25, rs_seen ps)] ++ rs_cur2 rsegs cx rest r)) by (pa_list; pa_from Hat).
    eapply pa_at_move; [exact Hat'|]. pa_kept Hkeep ltac:(apply Hall). }
  assert (Hcore3 : rs_core rsegs B MT cx (rs_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3).
  { refine (pa_core_step B MT MTL cx _ (fun _ => False) _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 _ Hfr Hperm Hio Hmo Hmem _);
    [pa_regs234 Hkeep | intros a []]. }
  assert (Hfsh3 : rs_fsh_at rsegs cx W3 mem3 rs_P0).
  { unfold rs_fsh_at in *. eapply rm_fsh_kept; [exact Hfsh|]. intros j Hj. apply Hall. }
  assert (Hpp3 : rs_pp_at rsegs cx W3 mem3 (pc_image (PbCut sh ps None))).
  { unfold rs_pp_at in *. eapply (rm_bytes_kept rsegs); [exact Hpp|]. intros x Hx. apply Hall. }
  destruct (Z.eqb_spec (Z.of_nat (length ps) - 1 + 1) np) as [Heq|Hne].
  + replace (Z.of_nat (length ps) - 1 + 1 =? np) with true by (symmetry; apply Z.eqb_eq; exact Heq).
    change (mkCfg (mkst regs3 (w64 PA_P1) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_P1 regs3 mem3 md3).
    apply (HP1 ly3 S3 W3 regs3 mem3 md3 sh np ps r).
    split.
    * split; [exact Hcore3|]. split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Hsuf|].
      split; [exact Hwf|]. split; [exact Hlen0|]. split; [exact Hsh|]. split; [exact Hnp|]. split; [lia | exact Hloop].
    * pa_list; pa_from Hat3.
  + replace (Z.of_nat (length ps) - 1 + 1 =? np) with false by (symmetry; apply Z.eqb_neq; exact Hne).
    change (mkCfg (mkst regs3 (w64 PA_N) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_N regs3 mem3 md3).
    apply (HN ly3 S3 W3 regs3 mem3 md3 sh np ps r Hlen).
    split; [exact Hcore3|]. split.
    * pa_list; first [pa_from Hat3 | idtac].
      cbn [rl_at]. refine (eq_trans R16 _). f_equal. lia.
    * split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Hsuf|]. split; [exact Hwf|].
      split; [exact Hsh|]. split; [exact Hnp|]. split; [lia|]. split; [exact Hnp3 | exact Hloop].
Qed.
End p.

(* ================================ the key: SELK -> SELS / SELI ================================ *)
Section pk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Lemma pa_piece_key : rs_piece_W4_key_stmt rsegs B MT.
Proof using MTL LAWS.
unfold rs_piece_W4_key_stmt. intros cx POST rest i Hst HSS HSI.
destruct Hst as (Hpre & Hc1 & Hlen0 & Hin0).
pose proof (pa_R_bounds B cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
pose proof (pa_blk_bounds B LAWS cx Hpre) as (PB1 & PB2 & FB1 & FB2 & FB3).
pose proof (pa_pp_blocks B LAWS cx Hpre) as (Ppin & Ppout & PA).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold rs_from_SELK. intros ly2 S2 W2 regs2 mem2 md2 sh np sel ps r Hlen Hcut.
destruct Hcut as (Hb & Hat & Hpp & Hsh7 & Hsel & Hselr).
pose proof Hb as (Hcore & Hfsh & Hin & Hsuf & Hwf & Hlen1 & Hpsl & Hsh & Hnp & Hps & Hnp3).
pose proof Hcore as (HJ & _ & _ & HPerm & _).
assert (Ppin2 : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Ppin]).
destruct (pa_img_bounds sh ps Hwf ltac:(lia)) as (IB1 & IB2 & IB3 & IB4).
unfold rs_at_cx in Hat.
pa_take Hat (LReg 9) (e_R (x_e cx)) A9. pa_take Hat (LReg 27) (e_pp (x_e cx)) A27.
pa_take Hat (LReg 21) (e_pp (x_e cx) + 0x4000) A21. pa_take Hat (LReg 20) (shadow_addr (e_pp (x_e cx) + 0x4000)) A20.
pa_take Hat (LReg 23) SHADOW_OFF A23. pa_take Hat (LReg 10) (rs_plen sh ps) A10. pa_take Hat (LReg 11) sel A11.
pa_take Hat (LReg 12) (rs_plen sh ps - 0x3ffd) A12. pa_take Hat (LReg 25) (rs_seen ps) A25.
pa_take Hat (LCell XR 0xe0) (-0x4001) Ae0. pa_take Hat (LCell XR 0xe8) (-0x3ffd) Ae8.
pa_take Hat (LCell XR 0x38) 0x10003 A38. pa_take Hat (LCell XR 0x48) 0x80001 A48.
assert (M1 : (-0x4001) mod 2 ^ 64 = 2 ^ 64 - 0x4001) by reflexivity.
assert (M2 : (-0x3ffd) mod 2 ^ 64 = 2 ^ 64 - 0x3ffd) by reflexivity.
rewrite M1 in Ae0. rewrite M2 in Ae8. rewrite Z.mod_small in A38, A48 by lia.
assert (Hseen : rs_seen ps = 0 \/ rs_seen ps = 1) by (unfold rs_seen; destruct (existsb _ _); cbn; lia).
assert (Hplen : rs_plen sh ps = Z.of_nat (length (pc_buf (PbCut sh ps None)))) by reflexivity.
assert (Alen : val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + 0x4000) 8 (rs_plen sh ps)).
{ rewrite Hplen. unfold rs_pp_at, pc_image in Hpp.
  assert (Hb16 : Z.of_nat (length (pc_buf (PbCut sh ps None))) <= Layout.POD_BUF_MAX) by (unfold Layout.POD_BUF_MAX; lia).
  exact (rm_pp_len rsegs _ _ _ _ _ _ Hb16 IB3 IB4 _ _ _ Hpp). }
eapply SRr_bind.
{ refine (pa_key B MT MTL LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (e_pp (x_e cx)) (rs_plen sh ps) sel (rs_seen ps)
    HJ A9 A27 A21 A20 A23 A10 A11 A12 A25 RB1 RB2 RB3 Ppin2 Ppout Ae0 Ae8 A38 A48 Alen _ _ Hsel Hseen); lia. }
intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
destruct HR as (R10 & Rpp & Rlen & R88 & Rd0 & Ra0).
set (R := e_R (x_e cx)) in *. set (pp := e_pp (x_e cx)) in *. set (F := e_F (x_e cx)) in *.
set (plen := rs_plen sh ps) in *.
assert (Hcore3 : rs_core rsegs B MT cx (rs_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3).
{ refine (pa_core_step B MT MTL cx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 _ Hfr Hperm Hio Hmo Hmem _).
  - pa_regs234 Hkeep.
  - intros a Ha. right. destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]];
    [apply pa_E1_pp | apply pa_E1_pp | apply pa_E1_R | apply pa_E1_R | apply pa_E1_R];
    fold pp R; unfold Layout.PP_SIZE; lia. }
assert (Hfsh3 : rs_fsh_at rsegs cx W3 mem3 rs_P0).
{ unfold rs_fsh_at in *. eapply rm_fsh_kept; [exact Hfsh|]. intros j Hj.
  replace (Z.of_nat (length rs_P0)) with 52 in Hj by reflexivity. fold F.
  assert (F8 : 0 <= F / 8 <= 0xfffffff0000) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in PA. unfold shadow_addr, SHADOW_OFF.
  apply Hmem; [lia|]. unfold Layout.PP_SIZE in *. lia. }
assert (Hkept : forall l, rs_at rsegs (w_H W2) mem2 regs2 (x_e cx) l ->
  Forall (fun f => pa_kept_loc (x_e cx) regs2 regs3 (w_H W2) (w_H W3) mem2 mem3 (fst f)) l ->
  rs_at rsegs (w_H W3) mem3 regs3 (x_e cx) l) by (intros l H1 H2; exact (pa_at_move _ _ _ _ _ _ _ _ H1 H2)).
assert (Hat3 : rs_at rsegs (w_H W3) mem3 regs3 (x_e cx)
  (rs_Rc rsegs cx ++ [(LReg 20, shadow_addr (pp + 0x4000)); (LReg 25, rs_seen ps)] ++ rs_Kc rsegs cx sh np ++
   [(LCell XR 0xb8, Z.of_nat (length ps))] ++ rs_cur2 rsegs cx rest r)).
{ apply Hkept; [pa_list; pa_from Hat|].
  cbn [rs_L_N rs_L_SEL rs_L_KEY rs_L_P rs_Rc rs_Rc0 rs_Kc rs_cur2 app];
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst pa_kept_loc rl_xv].
  all: try (apply Hkeep; [cbv; discriminate | pa_notin]).
  all: try (let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; fold R pp; apply Hmem; [unfold Layout.PP_SIZE in *; lia | unfold Layout.PP_SIZE in *; lia]).
  all: let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; fold R pp; apply Hmem;
    unfold T_SEG_STK, ASTACK, Layout.PP_SIZE in *; lia. }
assert (Hpp3 : forall kk, rm_bytes rsegs (w_H W3) mem3 (pp + plen) (le32 kk ++ le32 0) ->
  rs_pp_at rsegs cx W3 mem3 (rs_img_key sh ps kk)).
{ intros kk Nx. unfold rs_pp_at, rs_img_key. fold pp.
  unfold rs_pp_at, pc_image in Hpp. fold pp in Hpp.
  eapply (pa_pp_append (w_H W2) mem2 (w_H W3) mem3 pp); [| exact IB3 | exact IB4 | exact Hpp | | |].
  - rewrite length_app, !length_le32. rewrite Nat2Z.inj_add. unfold Layout.POD_BUF_MAX. lia.
  - exact Nx.
  - rewrite length_app, !length_le32, Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. unfold Layout.OFF_LEN.
    rewrite <- Hplen. fold plen. replace (plen + Z.of_nat 8) with (plen + 8) by reflexivity. exact Rlen.
  - intros y Hy Hx Hl. rewrite length_app, !length_le32 in Hx. rewrite <- Hplen in Hx. fold plen in Hx.
    apply Hmem; [unfold Layout.PP_SIZE in *; lia|]. unfold T_SEG_STK, ASTACK, Layout.OFF_LEN, Layout.PP_SIZE in *.
    cbn [Nat.add Z.of_nat Pos.of_succ_nat] in Hx. lia. }
assert (Hseen01 : rs_first ps = 1 - rs_seen ps) by (unfold rs_first, rs_seen; destruct (existsb _ _); reflexivity).
assert (HatK : forall K88 Kd0, val_mem rsegs (mrestrict (w_H W3) mem3) (R + 0x88) 8 K88 -> 0 <= K88 < 2 ^ 64 ->
  val_mem rsegs (mrestrict (w_H W3) mem3) (R + 0xd0) 8 Kd0 -> 0 <= Kd0 < 2 ^ 64 ->
  rs_at rsegs (w_H W3) mem3 regs3 (x_e cx)
  (rs_Rc rsegs cx ++ [(LReg 20, shadow_addr (pp + 0x4000)); (LReg 10, rs_at_of sh ps - 0x3ffd)] ++ rs_Kc rsegs cx sh np ++
   [(LCell XR 0xb8, Z.of_nat (length ps)); (LCell XR 0xa0, rs_at_of sh ps);
    (LCell XR 0x88, K88); (LCell XR 0xd0, Kd0)] ++ rs_cur2 rsegs cx rest r)).
{ intros K88 Kd0 V88 B88 Vd0 Bd0. pa_list; first [pa_from Hat3 | idtac].
  - cbn [rl_at]. refine (eq_trans R10 _). unfold rs_at_of. fold plen. first [reflexivity | f_equal; lia].
  - cbn [rl_at rl_xv]. fold R. unfold rs_at_of. fold plen. rewrite Z.mod_small by (unfold Layout.PP_SIZE in *; lia). exact Ra0.
  - cbn [rl_at rl_xv]. fold R. rewrite Z.mod_small by lia. exact V88.
  - cbn [rl_at rl_xv]. fold R. rewrite Z.mod_small by lia. exact Vd0. }
destruct ((sel mod 4 =? 0) || Z.testbit sel 4) eqn:Ec.
- change (mkCfg (mkst regs3 (w64 PA_SELI) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_SELI regs3 mem3 md3).
  apply (HSI ly3 S3 W3 regs3 mem3 md3 sh np sel ps r Hlen).
  split; [split; [exact Hcore3|]; split; [exact Hfsh3|]; repeat (split; [eassumption|]); repeat split; assumption|].
  split.
  + unfold rs_at_cx, rs_L_KEY. apply HatK.
    * destruct (Z.eqb_spec (sel mod 4) 0); [exact R88 | exact R88].
    * destruct (sel mod 4 =? 0); lia.
    * destruct (Z.eqb_spec (sel mod 4) 0) as [E0|E0].
      -- exact Rd0.
      -- rewrite Hseen01. destruct Hseen as [E1|E1]; rewrite E1 in Rd0 |- *; cbn in Rd0 |- *; exact Rd0.
    * destruct (sel mod 4 =? 0); [lia | rewrite Hseen01; lia].
  + split; [apply Hpp3; unfold rs_key_of; exact Rpp|].
    split; [exact Hsh7|]. split; [exact Hsel|]. split; [|exact Hselr].
    apply orb_true_iff in Ec as [E|E]; [left; apply Z.eqb_eq; exact E | right; exact E].
- change (mkCfg (mkst regs3 (w64 PA_SELS) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_SELS regs3 mem3 md3).
  apply orb_false_iff in Ec as [E0 E4]. apply Z.eqb_neq in E0.
  apply (HSS ly3 S3 W3 regs3 mem3 md3 sh np sel ps r Hlen).
  split; [split; [exact Hcore3|]; split; [exact Hfsh3|]; repeat (split; [eassumption|]); repeat split; assumption|].
  split.
  + unfold rs_at_cx, rs_L_KEY. replace (sel mod 4 =? 0) with false in * by (symmetry; apply Z.eqb_neq; exact E0).
    apply HatK; [exact R88 | lia | | rewrite Hseen01; lia].
    destruct Hseen as [E1|E1]; rewrite E1 in Rd0; rewrite Hseen01, E1; cbn in Rd0 |- *; exact Rd0.
  + replace (sel mod 4 =? 0) with false in Rpp by (symmetry; apply Z.eqb_neq; exact E0).
    split; [apply Hpp3; exact Rpp|].
    split; [exact Hsh7|]. split; [exact Hsel|]. split; [exact E0|]. split; [exact E4 | exact Hselr].
Qed.
End pk.

(* ================================ the shape-7 Int pod: SEL7 -> LATCH7 ================================ *)
Section pi. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* the memset wrapper's contract (__asan_memset 0x51570), which the Int pod block's pad calls *)
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet 0x51570.

Lemma pa_piece_int7 : rs_piece_W4_int7_stmt rsegs B MT.
Proof using MTL LAWS AMEMSET.
unfold rs_piece_W4_int7_stmt. intros cx POST rest i Hst HL7.
destruct Hst as (Hpre & Hc1 & Hlen0 & Hin0).
pose proof (pa_R_bounds B cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
pose proof (pa_blk_bounds B LAWS cx Hpre) as (PB1 & PB2 & FB1 & FB2 & FB3).
pose proof (pa_pp_blocks B LAWS cx Hpre) as (Ppin & Ppout & PA).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hpre as Hpre'. unfold rs_pre, rl_seg_pre in Hpre'.
destruct Hpre' as (_ & _ & G2 & G3 & G4 & _).
unfold rs_from_SEL7. intros ly2 S2 W2 regs2 mem2 md2 np ps r Hlen Hcut.
destruct Hcut as (Hb & Hat & Hpp & Hr).
pose proof Hb as (Hcore & Hfsh & Hin & Hsuf & Hwf & Hlen1 & Hpsl & Hsh & Hnp & Hps & Hnp3).
pose proof Hcore as (HJ & Hr234 & _ & HPerm & _).
assert (Ppin2 : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Ppin]).
destruct (pa_img_bounds 7 ps Hwf ltac:(lia)) as (IB1 & IB2 & IB3 & IB4).
unfold rs_at_cx in Hat.
pa_take Hat (LReg 9) (e_R (x_e cx)) A9. pa_take Hat (LReg 27) (e_pp (x_e cx)) A27.
pa_take Hat (LReg 21) (e_pp (x_e cx) + 0x4000) A21. pa_take Hat (LReg 20) (shadow_addr (e_pp (x_e cx) + 0x4000)) A20.
pa_take Hat (LReg 23) SHADOW_OFF A23. pa_take Hat (LReg 10) (rs_plen 7 ps) A10.
pa_take Hat (LReg 12) (rs_plen 7 ps - 0x3ffd) A12.
pa_take Hat (LCell XR 0xb8) (Z.of_nat (length ps)) Ab8.
pa_take Hat (LCell XR 0xe0) (-0x4001) Ae0. pa_take Hat (LCell XR 0xe8) (-0x3ffd) Ae8.
assert (M1 : (-0x4001) mod 2 ^ 64 = 2 ^ 64 - 0x4001) by reflexivity.
assert (M2 : (-0x3ffd) mod 2 ^ 64 = 2 ^ 64 - 0x3ffd) by reflexivity.
rewrite M1 in Ae0. rewrite M2 in Ae8. rewrite Z.mod_small in Ab8 by lia.
assert (A2 : getr regs2 2 = w64 (e_R (x_e cx))) by (exact (eq_trans (Hr234 2 ltac:(lia)) RB6)).
assert (A3 : getr regs2 3 = w64 (as_gp B)) by (exact (eq_trans (Hr234 3 ltac:(lia)) G3)).
assert (A4 : getr regs2 4 = w64 (as_tp B)) by (exact (eq_trans (Hr234 4 ltac:(lia)) G4)).
assert (Hplen : rs_plen 7 ps = Z.of_nat (length (pc_buf (PbCut 7 ps None)))) by reflexivity.
assert (Alen : val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + 0x4000) 8 (rs_plen 7 ps)).
{ rewrite Hplen. unfold rs_pp_at, pc_image in Hpp.
  assert (Hb16 : Z.of_nat (length (pc_buf (PbCut 7 ps None))) <= Layout.POD_BUF_MAX) by (unfold Layout.POD_BUF_MAX; lia).
  exact (rm_pp_len rsegs _ _ _ _ _ _ Hb16 IB3 IB4 _ _ _ Hpp). }
eapply SRr_bind.
{ refine (pa_int7 B MT MTL LAWS AMEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (e_pp (x_e cx)) (Z.of_nat (length ps)) (rs_plen 7 ps)
    HJ A2 A3 A4 A9 A27 A21 A20 A23 A10 A12 RB1 RB2 RB3 Ppin2 Ppout Ab8 Ae0 Ae8 Alen _ _ _ _); rewrite ?Hplen; lia. }
intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
destruct HR as (R16 & Rpp & Rlen).
set (R := e_R (x_e cx)) in *. set (pp := e_pp (x_e cx)) in *. set (F := e_F (x_e cx)) in *.
set (plen := rs_plen 7 ps) in *.
assert (SP : spZ (x_regs cx) = R).
{ unfold spZ. rewrite RB6. unfold w64. apply unsigned_lit_small. lia. }
assert (Hcore3 : rs_core rsegs B MT cx (rs_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3).
{ refine (pa_core_step B MT MTL cx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 _ Hfr Hperm Hio Hmo Hmem _).
  - pa_regs234 Hkeep.
  - intros a Ha. rewrite SP. destruct Ha as [Ha|[Ha|Ha]].
    + right. apply pa_E1_pp. fold pp. unfold Layout.PP_SIZE. lia.
    + right. apply pa_E1_pp. fold pp. unfold Layout.PP_SIZE. lia.
    + left. unfold T_SEG_STK, ASTACK, ESTACK in *. lia. }
assert (Hfsh3 : rs_fsh_at rsegs cx W3 mem3 rs_P0).
{ unfold rs_fsh_at in *. eapply rm_fsh_kept; [exact Hfsh|]. intros j Hj.
  replace (Z.of_nat (length rs_P0)) with 52 in Hj by reflexivity. fold F.
  assert (F8 : 0 <= F / 8 <= 0xfffffff0000) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in PA. unfold shadow_addr, SHADOW_OFF.
  apply Hmem; [lia|]. unfold T_SEG_STK, ASTACK, ESTACK, Layout.PP_SIZE in *. lia. }
assert (Hat3 : rs_at rsegs (w_H W3) mem3 regs3 (x_e cx)
  (rs_Rc rsegs cx ++ [(LReg 20, shadow_addr (pp + 0x4000)); (LReg 25, rs_seen ps)] ++ rs_Kc rsegs cx 7 np ++
   rs_cur2 rsegs cx rest r)).
{ eapply pa_at_move; [pa_list; pa_from Hat|].
  cbn [rs_L_N rs_L_SEL rs_L_KEY rs_L_P rs_Rc rs_Rc0 rs_Kc rs_cur2 app];
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst pa_kept_loc rl_xv].
  all: try (apply Hkeep; [cbv; discriminate | pa_notin]).
  all: let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; fold R pp; apply Hmem;
    unfold T_SEG_STK, ASTACK, ESTACK, Layout.PP_SIZE in *; lia. }
assert (Hpp3 : rs_pp_at rsegs cx W3 mem3 (pc_image (PbCut 7 (ps ++ [(0, PInt 0)]) None))).
{ unfold rs_pp_at. rewrite pa_img7. fold pp.
  unfold rs_pp_at, pc_image in Hpp. fold pp in Hpp.
  assert (Lx : length (prop_bytes 7 (0, PInt 0)) = 16%nat) by reflexivity.
  eapply (pa_pp_append (w_H W2) mem2 (w_H W3) mem3 pp); [| exact IB3 | exact IB4 | exact Hpp | | |].
  - rewrite Lx, Nat2Z.inj_add. unfold Layout.POD_BUF_MAX. lia.
  - rewrite <- Hplen. fold plen.
    replace (map (fun x : byte => bv_unsigned x) (prop_bytes 7 (0, PInt 0))) with pa_int7_bytes by (vm_compute; reflexivity).
    exact Rpp.
  - rewrite Lx, Nat2Z.inj_add, <- Hplen. fold plen. unfold Layout.OFF_LEN.
    replace (plen + Z.of_nat 16) with (plen + 16) by reflexivity. exact Rlen.
  - intros y Hy Hx Hl. rewrite Lx, <- Hplen in Hx. fold plen in Hx.
    apply Hmem; [unfold Layout.PP_SIZE in *; lia|]. unfold T_SEG_STK, ASTACK, ESTACK, Layout.OFF_LEN, Layout.PP_SIZE in *.
    cbn [Z.of_nat Pos.of_succ_nat] in Hx. lia. }
change (mkCfg (mkst regs3 (w64 PA_LATCH7) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_LATCH7 regs3 mem3 md3).
apply (HL7 ly3 S3 W3 regs3 mem3 md3 7 np (ps ++ [(0, PInt 0)]) r ltac:(rewrite length_app, Hlen; cbn; lia)).
split.
- split; [exact Hcore3|]. split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Hsuf|].
  split; [apply pa_wf7; [exact Hwf | lia]|]. split; [exact Hsh|]. split; [exact Hnp|].
  split; [rewrite length_app; cbn; lia|]. split; [exact Hnp3|].
  rewrite length_app, Nat.add_1_r, pa_loop7, <- Hpsl, <- Hr. reflexivity.
- unfold rs_at_cx. rewrite pa_seen7. pa_list; first [pa_from Hat3 | idtac].
  cbn [rl_at]. refine (eq_trans R16 _). rewrite length_app. cbn. f_equal. lia.
Qed.
End pi.

(* ================================ the selector: N -> SEL7 / SELK ================================ *)
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

Section ps. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

Lemma pa_piece_sel : rs_piece_W4_sel_stmt rsegs B MT.
Proof using MTL LAWS.
unfold rs_piece_W4_sel_stmt. intros cx POST rest i Hst HS7 HSK.
destruct Hst as (Hpre & Hc1 & Hlen0 & Hin0).
pose proof (pa_R_bounds B cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
pose proof (pa_blk_bounds B LAWS cx Hpre) as (PB1 & PB2 & FB1 & FB2 & FB3).
pose proof (pa_pp_blocks B LAWS cx Hpre) as (Ppin & Ppout & PA).
assert (PA' : e_pp (x_e cx) + Layout.PP_SIZE <= 0x7fff7fff \/ 0x10007fff8000 <= e_pp (x_e cx))
  by (destruct PA as [A|[A _]]; [left; exact A | right; exact A]).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold rs_from_N. intros ly2 S2 W2 regs2 mem2 md2 sh np ps r Hlen Hcut.
destruct Hcut as (Hcore & Hat & Hfsh & Hpp & Hin & Hsuf & Hwf & Hsh & Hnp & Hps & Hnp3 & Hloop).
pose proof Hcore as (HJ & Hr234 & _ & HPerm & _).
assert (Ppin2 : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Ppin]).
destruct (pa_img_bounds sh ps Hwf ltac:(lia)) as (IB1 & IB2 & IB3 & IB4).
pose proof Hin as (Hleft & Hgarr & Hra & Hhull & Hamr & Hsrc0 & Hsrcn & Hapart).
pose proof Hsuf as (j & Hj & Er).
assert (Lr : length r = (length rest - j)%nat) by (rewrite Er; apply length_skipn).
assert (Hcur : rs_cur rsegs cx rest r = e_src (x_e cx) + Z.of_nat j) by (unfold rs_cur; rewrite Lr; lia).
assert (Hsh8 : 0 <= sh < 8) by (exact (proj1 Hwf)).
unfold rs_at_cx in Hat.
pa_take Hat (LReg 9) (e_R (x_e cx)) A9. pa_take Hat (LReg 16) (Z.of_nat (length ps)) A16.
pa_take Hat (LReg 27) (e_pp (x_e cx)) A27.
pa_take Hat (LReg 21) (e_pp (x_e cx) + 0x4000) A21. pa_take Hat (LReg 20) (shadow_addr (e_pp (x_e cx) + 0x4000)) A20.
pa_take Hat (LReg 23) SHADOW_OFF A23.
pa_take Hat (LCell XR 0x98) sh A98. pa_take Hat (LCell XR 0xe8) (-0x3ffd) Ae8.
pa_take Hat (LCell XR 0xc8) (rs_cur rsegs cx rest r) Ac8. pa_take Hat (LCell XR 0xf8) (Z.of_nat (length r)) Af8.
assert (M2 : (-0x3ffd) mod 2 ^ 64 = 2 ^ 64 - 0x3ffd) by reflexivity. rewrite M2 in Ae8.
rewrite Z.mod_small in A98 by lia. rewrite Z.mod_small in Af8 by lia.
rewrite Z.mod_small in Ac8 by (rewrite Hcur; lia).
assert (Hplen : rs_plen sh ps = Z.of_nat (length (pc_buf (PbCut sh ps None)))) by reflexivity.
assert (Alen : val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + 0x4000) 8 (rs_plen sh ps)).
{ rewrite Hplen. unfold rs_pp_at, pc_image in Hpp.
  assert (Hb16 : Z.of_nat (length (pc_buf (PbCut sh ps None))) <= Layout.POD_BUF_MAX) by (unfold Layout.POD_BUF_MAX; lia).
  exact (rm_pp_len rsegs _ _ _ _ _ _ Hb16 IB3 IB4 _ _ _ Hpp). }
assert (Hinp : 0 < Z.of_nat (length r) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (rs_cur rsegs cx rest r) 1 (fst (fuzz_u8 r)) /\ 0 <= fst (fuzz_u8 r) < 256 /\
  range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (rs_cur rsegs cx rest r) 1 /\
  amem_range (rs_cur rsegs cx rest r) 1 /\ ~ (e_R (x_e cx) <= rs_cur rsegs cx rest r < e_R (x_e cx) + 0x138) /\
  ~ (e_pp (x_e cx) <= rs_cur rsegs cx rest r < e_pp (x_e cx) + Layout.PP_SIZE)).
{ intros Hnz. rewrite Hcur. destruct r as [|bb r''] eqn:Er'; [cbn in Hnz; lia|]. cbn [fuzz_u8 fst].
  destruct (pa_nth_skipn rest j bb r'' (eq_sym Er)) as (Hjl & Hnth).
  destruct (pa_input_now B MT LAWS cx rest ly2 S2 W2 regs2 mem2 md2 (Z.of_nat j) Hpre Hin Hcore Hfsh ltac:(lia))
    as (V & RA).
  assert (Hb : nth (Z.to_nat (Z.of_nat j)) (rs_u8s rest) 0 = bv_unsigned bb).
  { rewrite Nat2Z.id. unfold rs_u8s. rewrite (nth_indep _ _ ((fun x : byte => bv_unsigned x) (Z_to_bv 8 0))) by (rewrite length_map; lia).
    rewrite map_nth, Hnth. reflexivity. }
  rewrite Hb in V. destruct (Hapart (e_src (x_e cx) + Z.of_nat j) ltac:(lia)) as (N1 & N2 & N3).
  split; [exact V|]. split; [pose proof (bv_unsigned_in_range 8 bb) as X; change (bv_modulus 8) with 256 in X; lia|].
  split; [exact RA|]. split; [unfold amem_range in *; lia|]. split; [|exact N3].
  intros X. apply N2. unfold rl_inw. cbn [hi_w1 role_himg_A].
  apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rl_xv]. lia. }
eapply SRr_bind.
{ refine (pa_sel B MT MTL LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (e_pp (x_e cx)) (Z.of_nat (length ps)) sh
    (rs_plen sh ps) (Z.of_nat (length r)) (rs_cur rsegs cx rest r) (fst (fuzz_u8 r))
    HJ A9 A16 A27 A21 A20 A23 RB1 RB2 RB3 Ppin2 A98 Hsh8 Ae8 Ac8 Af8 Alen _ _ _ _ _ Hinp); rewrite ?Hplen, ?Hcur; lia. }
intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
destruct HR as (R10 & R11 & R12 & Vb8 & Vc8 & Vf8).
set (R := e_R (x_e cx)) in *. set (pp := e_pp (x_e cx)) in *. set (F := e_F (x_e cx)) in *.
(* the cursor after the selector byte *)
assert (Hstep : getr regs3 11 = w64 (fst (fuzz_u8 r)) /\
  val_mem rsegs (mrestrict (w_H W3) mem3) (R + 0xc8) 8 (rs_cur rsegs cx rest (snd (fuzz_u8 r)) mod 2 ^ 64) /\
  val_mem rsegs (mrestrict (w_H W3) mem3) (R + 0xf8) 8 (Z.of_nat (length (snd (fuzz_u8 r))) mod 2 ^ 64)).
{ rewrite Hcur in Vc8. destruct r as [|bb r''] eqn:Er'.
  - cbn [fuzz_u8 fst snd length Z.of_nat Z.eqb] in R11, Vc8, Vf8 |- *.
    rewrite Hcur, !Z.mod_small by lia. split; [exact R11|]. split; [exact Vc8 | exact Vf8].
  - cbn [fuzz_u8 fst snd length] in R11, Vc8, Vf8 |- *.
    replace (Z.of_nat (S (length r'')) =? 0) with false in R11, Vc8, Vf8 by (symmetry; apply Z.eqb_neq; lia).
    unfold rs_cur. cbn [length] in Lr. rewrite !Z.mod_small by lia.
    split; [exact R11|]. split.
    + replace (e_src (x_e cx) + Z.of_nat (length rest) - Z.of_nat (length r'')) with (e_src (x_e cx) + Z.of_nat j + 1) by lia.
      exact Vc8.
    + replace (Z.of_nat (length r'')) with (Z.of_nat (S (length r'')) - 1) by lia. exact Vf8. }
destruct Hstep as (R11' & Vc8' & Vf8').
assert (Hcore3 : rs_core rsegs B MT cx (rs_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3).
{ refine (pa_core_step B MT MTL cx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 _ Hfr Hperm Hio Hmo Hmem _).
  - pa_regs234 Hkeep.
  - intros a Ha. right. apply pa_E1_R. fold R. lia. }
assert (Hfsh3 : rs_fsh_at rsegs cx W3 mem3 rs_P0).
{ unfold rs_fsh_at in *. eapply rm_fsh_kept; [exact Hfsh|]. intros jj Hjj.
  replace (Z.of_nat (length rs_P0)) with 52 in Hjj by reflexivity. fold F.
  assert (F8 : 0 <= F / 8 <= 0xfffffff0000) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  unfold shadow_addr, SHADOW_OFF. apply Hmem; [lia|]. unfold T_SEG_STK, ASTACK in *. lia. }
assert (Hpp3 : rs_pp_at rsegs cx W3 mem3 (pc_image (PbCut sh ps None))).
{ unfold rs_pp_at in *. eapply (rm_bytes_kept rsegs); [exact Hpp|]. intros x Hx.
  assert (Hb16 : Z.of_nat (length (pc_buf (PbCut sh ps None))) <= 16384) by lia.
  unfold pc_image in Hx. rewrite (length_pp_image _ _ _ _ _ _ Hb16 IB3 IB4) in Hx. fold pp in Hx.
  apply Hmem; unfold T_SEG_STK, ASTACK, Layout.PP_SIZE in *; lia. }
assert (Hat3 : rs_at rsegs (w_H W3) mem3 regs3 (x_e cx)
  (rs_Rc rsegs cx ++ [(LReg 20, shadow_addr (pp + 0x4000)); (LReg 25, rs_seen ps)] ++ rs_Kc rsegs cx sh np)).
{ eapply pa_at_move; [pa_list; pa_from Hat|].
  cbn [rs_L_N rs_L_SEL rs_L_KEY rs_L_P rs_Rc rs_Rc0 rs_Kc rs_cur2 app];
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst pa_kept_loc rl_xv].
  all: try (apply Hkeep; [cbv; discriminate | pa_notin]).
  all: let jj := fresh "jj" in let Hjj := fresh "Hjj" in intros jj Hjj; fold R pp; apply Hmem;
    unfold T_SEG_STK, ASTACK, Layout.PP_SIZE in *; lia. }
assert (HatS : rs_at rsegs (w_H W3) mem3 regs3 (x_e cx) (rs_L_SEL rsegs cx sh np ps rest (snd (fuzz_u8 r)))).
{ pa_list; first [pa_from Hat3 | idtac].
  - cbn [rl_at]. exact (eq_trans R10 eq_refl).
  - cbn [rl_at]. exact (eq_trans R12 eq_refl).
  - cbn [rl_at rl_xv]. fold R. rewrite Z.mod_small by lia. exact Vb8.
  - cbn [rl_at rl_xv]. fold R. exact Vc8'.
  - cbn [rl_at rl_xv]. fold R. exact Vf8'. }
assert (Hbase : forall sh', sh' = sh -> rs_prop_base rsegs B MT cx sh' np ps rest (snd (fuzz_u8 r)) ly3 S3 W3 regs3 mem3 md3).
{ intros sh' ->. split; [exact Hcore3|]. split; [exact Hfsh3|]. split; [exact Hin|].
  split; [apply pa_suffix_step; exact Hsuf|]. split; [exact Hwf|]. split; [exact Hlen0|].
  split; [rewrite <- Hloop; reflexivity|]. split; [exact Hsh|]. split; [exact Hnp|]. split; [exact Hps | exact Hnp3]. }
destruct (Z.eqb_spec sh 7) as [E7|E7].
- change (mkCfg (mkst regs3 (w64 PA_SEL7) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_SEL7 regs3 mem3 md3).
  apply (HS7 ly3 S3 W3 regs3 mem3 md3 np ps (snd (fuzz_u8 r)) Hlen).
  rewrite E7 in HatS, Hpp3.
  split; [exact (Hbase 7 (eq_sym E7))|]. split; [exact HatS|]. split; [exact Hpp3|].
  rewrite <- E7, <- Hloop. reflexivity.
- change (mkCfg (mkst regs3 (w64 PA_SELK) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_SELK regs3 mem3 md3).
  apply (HSK ly3 S3 W3 regs3 mem3 md3 sh np (fst (fuzz_u8 r)) ps (snd (fuzz_u8 r)) Hlen).
  split; [exact (Hbase sh eq_refl)|]. split.
  + unfold rs_at_cx. apply pa_at_app; [exact HatS|]. constructor; [|constructor]. cbn [rl_at fst snd]. exact R11'.
  + split; [exact Hpp3|]. split; [exact E7|].
    split; [destruct r as [|bb r'']; cbn [fuzz_u8 fst]; [lia | pose proof (bv_unsigned_in_range 8 bb) as X; change (bv_modulus 8) with 256 in X; lia]|].
    rewrite <- Hloop. cbn [snd]. destruct (fuzz_u8 r); reflexivity.
Qed.
End ps.

Print Assumptions pa_piece_sel.
Print Assumptions pa_piece_int7.
Print Assumptions pa_piece_key.
Print Assumptions pa_piece_latch.
