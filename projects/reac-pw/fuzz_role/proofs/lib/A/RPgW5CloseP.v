(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; addresses from the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6): the piece lemma of the params Struct's close
   in LLVMFuzzerTestOneInput (0x7ff88), CL 0x81ccc -> LATCH 0x81d6c, as lib/A/RPgSeg.v states it
   (rs_piece_W5_close_stmt). Proves no function (kind: segment lemma).

   HOW. The cut CL gives the code's facts (registers, real-frame cells, pp->len from the first block's image); the
   core walk (lib/A/RPgW5Close.v w5_close_core) runs from them to 0x81d6c; the cut LATCH is rebuilt from its post:
   the journal and frame part (RPgW5Seg w5_core_post), the (location, value) facts (kept, and R+0xc8 := the cursor),
   the frame's shadow (kept), the first block's image (Model.pc_buf_close and the two flag words when the Struct is
   the first params property: RPgW5Seg w5_img_close_eq, w5_img_gen) and the model facts (Model.props_loop's Struct
   arm, from the cut's tie of the count and the pods to the input). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgMem RPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgW5Kit RPgW5Seg RPgW5Close.
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
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

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
destruct Hst as (Hpre & Hc1 & Hlen0 & Hin0).
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
pose proof (w5_at_reg _ _ _ _ _ 20 (shadow_addr (e_pp (x_e cx) + 0x4000)) Hat ltac:(w5_in)) as A20.
pose proof (w5_at_reg _ _ _ _ _ 21 (e_pp (x_e cx) + 0x4000) Hat ltac:(w5_in)) as A21.
pose proof (w5_at_reg _ _ _ _ _ 23 SHADOW_OFF Hat ltac:(w5_in)) as A23.
pose proof (w5_at_reg _ _ _ _ _ 25 (rs_cur rsegs cx rest r) Hat ltac:(w5_in)) as A25.
pose proof (w5_at_reg _ _ _ _ _ 27 (e_pp (x_e cx)) Hat ltac:(w5_in)) as A27.
pose proof (w5_at_cell _ _ _ _ _ 0xa0 (rs_at_of sh ps) Hat ltac:(w5_in)) as Va0.
pose proof (w5_at_cell _ _ _ _ _ 0xd0 (rs_first ps) Hat ltac:(w5_in)) as Vd0.
pose proof (w5_at_cell _ _ _ _ _ 0x50 (e_pp (x_e cx) + 0x400c) Hat ltac:(w5_in)) as V50.
pose proof (w5_at_cell _ _ _ _ _ 0x40 (e_pp (x_e cx) + 0x4010) Hat ltac:(w5_in)) as V40.
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
assert (Hcur : 0 <= rs_cur rsegs cx rest r < 2 ^ 64).
{ destruct Hin as (Hl & _ & _ & _ & _ & Hs0 & Hs63 & _). destruct Hsuf as (j & Hj & ->).
  unfold rs_cur. rewrite length_skipn. lia. }
rewrite Z.mod_small in Va0 by lia. rewrite Z.mod_small in Vd0 by lia.
rewrite Z.mod_small in V50 by (unfold PP_SIZE in *; lia). rewrite Z.mod_small in V40 by (unfold PP_SIZE in *; lia).
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
    (rs_first ps) (rs_cur rsegs cx rest r) HJ Ppin2 Ppout A2 A9 A20 A21 A23 A25 A27 Va0 Vd0 V50 V40 Vlen RB3 RB1 RB2
    Hat16 Hal H5440 Hfr Hcur). }
intros W3 c3 Hle Hpost.
assert (HEp : forall a, (e_pp (x_e cx) + rs_at_of sh ps <= a < e_pp (x_e cx) + rs_at_of sh ps + 4) \/
  (e_R (x_e cx) + 0xc8 <= a < e_R (x_e cx) + 0xd0) \/
  (rs_first ps = 1 /\ e_pp (x_e cx) + 0x400c <= a < e_pp (x_e cx) + 0x4014) -> rs_E1 rsegs cx a).
{ intros a [Ha|[Ha|[_ Ha]]].
  - right. unfold PP_SIZE. lia.
  - left. unfold rl_inw. cbn [hi_w1 role_himg_A].
    apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rl_xv]. lia.
  - right. unfold PP_SIZE. lia. }
assert (Hclob : forall r0, (r0 = 2 \/ r0 = 3 \/ r0 = 4) -> ~ In (Z_to_bv 5 r0) [10; 11; 12; 13; 14]%bv).
{ intros r0 [-> | [-> | ->]]; w5_notin. }
destruct (w5_core_post B MT MTL cx (rs_E1 rsegs cx) _ ly2 S2 W2 regs2 mem2 md2 0x81d6c [10; 11; 12; 13; 14]%bv _ W3 c3
  Hcore HEp Hclob Hpost) as (ly3 & S3 & regs3 & mem3 & md3 & -> & Hcore3 & Hkeep & Hmem & (Rsz & Rcur & Rfl)).
assert (Hsp : spZ regs2 = e_R (x_e cx)) by (unfold spZ; rewrite A2; apply unsigned_lit_small; lia).
(* every byte the piece did not write *)
assert (Kp : forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) ->
  ~ (e_pp (x_e cx) + rs_at_of sh ps <= a < e_pp (x_e cx) + rs_at_of sh ps + 4) ->
  ~ (e_R (x_e cx) + 0xc8 <= a < e_R (x_e cx) + 0xd0) ->
  ~ (rs_first ps = 1 /\ e_pp (x_e cx) + 0x400c <= a < e_pp (x_e cx) + 0x4014) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 H2 H3 H4. apply Hmem; [exact Ha | rewrite Hsp; exact H1 |]. intros [X|[X|X]]; auto. }
assert (Kc : forall a, e_R (x_e cx) <= a < e_R (x_e cx) + 0xc8 \/ e_R (x_e cx) + 0xd0 <= a < e_R (x_e cx) + 0x100 ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia; intros [_ X]; lia. }
(* ---- the cut LATCH ---- *)
change (cfg_at rsegs 0x81d6c regs3 mem3 md3) with (cfg_at rsegs RS_LATCH regs3 mem3 md3).
apply (HL ly3 S3 W3 regs3 mem3 md3 sh np (ps ++ [(POD_PROP_PARAMS, PStruct es)]) r);
  [rewrite length_app, Hlen; cbn [length]; lia|].
split.
- split; [exact Hcore3|].
  split.
  { unfold rs_fsh_at in *. eapply rm_fsh_kept; [exact Hfsh|]. intros j Hj.
    change (length rs_P0) with 52%nat in Hj.
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
- unfold rs_at_cx, rs_at.
  rewrite (w5_seen_close ps es).
  replace (Z.of_nat (length (ps ++ [(POD_PROP_PARAMS, PStruct es)])) - 1) with (Z.of_nat (length ps))
    by (rewrite length_app; cbn [length]; lia).
  cbn [rs_Rc rs_Rc0 rs_Kc rs_cur2 app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  all: first [ w5_kept Hat Hkeep Kc | (cbn [rl_at rl_xv]; rewrite Z.mod_small by lia; exact Rcur) ].
Qed.
End p.

Print Assumptions w5_piece_close.
