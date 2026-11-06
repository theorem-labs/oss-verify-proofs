(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5CloseP.v at ada533759b23 for reac-pw/fuzz_rate's
   image A: module paths changed; rate's pcs (CL 0x82484 -> LATCH 0x82528), cut lists (lib/A/RtPgSeg.v: the cursor in
   R+0x100, the six header cells rs_Hc, the frame's 56 shadow bytes) and segment start (rs_start_M01 with its own
   rt_fsh and rt_cut conjuncts); rm_ / rl_ become rtm_ / rt_. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses from the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): the piece lemma of the params Struct's close
   in LLVMFuzzerTestOneInput (0x80714), CL 0x82484 -> LATCH 0x82528, as lib/A/RtPgSeg.v states it
   (rs_piece_W5_close_stmt). Proves no function (kind: segment lemma).

   HOW. The cut CL gives the code's facts (registers, real-frame cells, pp->len from the first block's image); the
   core walk (lib/A/RtPgW5Close.v w5_close_core) runs from them to 0x82528; the cut LATCH is rebuilt from its post:
   the journal and frame part (RtPgW5Seg w5_core_post), the (location, value) facts (kept, and R+0x100 := the cursor),
   the frame's shadow (kept), the first block's image (Model.pc_buf_close and the two flag words when the Struct is
   the first params property: RtPgW5Seg w5_img_close_eq, w5_img_gen) and the model facts (Model.props_loop's Struct
   arm, from the cut's tie of the count and the pods to the input). *)
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
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgW5Kit RtPgW5Seg RtPgW5Close.
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

(* membership in a cut's (location, value) list, and a register outside a clobber list *)
Ltac w5_in := cbn [rs_Rc rs_Rc0 rs_Kc rs_Hc rs_cur2 app In fst snd]; repeat (first [left; reflexivity | right]).
Ltac w5_notin :=
let H := fresh "H" in intros H; cbn [In] in H;
repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]); exact H.
(* a location of the end cut that the piece kept: from the start cut's list Hat, its register outside the clobber
   list (Hkeep) or its 8 bytes in a range the piece did not write (Kc) *)
Ltac w5_kept Hat Hkeep Kc := lazymatch goal with |- rt_at _ _ _ _ _ ?l ?v =>
  apply (rtm_at_kept rsegs _ _ _ _ _ _ _ l v (proj1 (Forall_forall _ _) Hat (l, v) ltac:(w5_in)));
  cbn [rtm_keeps rt_xv];
  first [ apply Hkeep; [vm_compute; discriminate | w5_notin]
        | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; apply Kc; lia ] end.

(* ---- the model at the close ---- *)
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
assert (A2 : getr regs2 2 = w64 (q_R (x_e cx))).
{ rewrite <- (w5_getr5 regs2 2%bv 2 eq_refl). rewrite (Hr234 2 (or_introl eq_refl)).
  rewrite (w5_getr5 (x_regs cx) 2%bv 2 eq_refl). exact RB4. }
pose proof (w5_at_reg _ _ _ _ _ 9 (q_R (x_e cx)) Hat ltac:(w5_in)) as A9.
pose proof (w5_at_reg _ _ _ _ _ 22 (shadow_addr (q_pp (x_e cx) + 0x4000)) Hat ltac:(w5_in)) as A22.
pose proof (w5_at_reg _ _ _ _ _ 23 (q_pp (x_e cx) + 0x4000) Hat ltac:(w5_in)) as A23.
pose proof (w5_at_reg _ _ _ _ _ 18 SHADOW_OFF Hat ltac:(w5_in)) as A18.
pose proof (w5_at_reg _ _ _ _ _ 25 (rs_cur rsegs cx rest r) Hat ltac:(w5_in)) as A25.
pose proof (w5_at_reg _ _ _ _ _ 27 (q_pp (x_e cx)) Hat ltac:(w5_in)) as A27.
pose proof (w5_at_cell _ _ _ _ _ 0xe0 (rs_at_of sh ps) Hat ltac:(w5_in)) as Va0.
pose proof (w5_at_cell _ _ _ _ _ 0x110 (rs_first ps) Hat ltac:(w5_in)) as Vd0.
pose proof (w5_at_cell _ _ _ _ _ 0x88 (q_pp (x_e cx) + 0x400c) Hat ltac:(w5_in)) as V50.
pose proof (w5_at_cell _ _ _ _ _ 0x70 (q_pp (x_e cx) + 0x4010) Hat ltac:(w5_in)) as V40.
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
assert (Old : rtm_bytes rsegs (w_H W2) mem2 (q_pp (x_e cx)) (pc_image (PbCut sh ps (Some es)))) by exact Hpp.
assert (Vlen : val_mem rsegs (mrestrict (w_H W2) mem2) (q_pp (x_e cx) + 0x4000) 8 len).
{ refine (rtm_pp_len rsegs _ _ _ _ _ _ _ EB1 EB2 _ _ _ Old). unfold POD_BUF_MAX; lia. }
assert (Ppin2 : In (q_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Ppin).
(* ---- the core walk ---- *)
eapply SRr_bind.
{ change (cfg_at rsegs RS_CL regs2 mem2 md2) with (cfg_at rsegs 0x82484 regs2 mem2 md2).
  exact (w5_close_core B MT MTL LAWS (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx)
    (x_md0 cx) (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 (q_R (x_e cx)) (q_pp (x_e cx)) (rs_at_of sh ps) len
    (rs_first ps) (rs_cur rsegs cx rest r) HJ Ppin2 Ppout A2 A9 A22 A23 A18 A25 A27 Va0 Vd0 V50 V40 Vlen RB3 RB1 RB2
    Hat16 Hal H5440 Hfr Hcur). }
intros W3 c3 Hle Hpost.
assert (HEp : forall a, (q_pp (x_e cx) + rs_at_of sh ps <= a < q_pp (x_e cx) + rs_at_of sh ps + 4) \/
  (q_R (x_e cx) + 0x100 <= a < q_R (x_e cx) + 0x108) \/
  (rs_first ps = 1 /\ q_pp (x_e cx) + 0x400c <= a < q_pp (x_e cx) + 0x4014) -> rs_E1 rsegs cx a).
{ intros a [Ha|[Ha|[_ Ha]]].
  - right. unfold PP_SIZE. lia.
  - left. unfold rt_inw. cbn [hi_w1 rate_himg_A].
    apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rt_xv]. lia.
  - right. unfold PP_SIZE. lia. }
assert (Hclob : forall r0, (r0 = 2 \/ r0 = 3 \/ r0 = 4) -> ~ In (Z_to_bv 5 r0) [10; 11; 12; 13; 14]%bv).
{ intros r0 [-> | [-> | ->]]; w5_notin. }
destruct (w5_core_post B MT MTL cx (rs_E1 rsegs cx) _ ly2 S2 W2 regs2 mem2 md2 0x82528 [10; 11; 12; 13; 14]%bv _ W3 c3
  Hcore HEp Hclob Hpost) as (ly3 & S3 & regs3 & mem3 & md3 & -> & Hcore3 & Hkeep & Hmem & (Rsz & Rcur & Rfl)).
assert (Hsp : spZ regs2 = q_R (x_e cx)) by (unfold spZ; rewrite A2; apply unsigned_lit_small; lia).
(* every byte the piece did not write *)
assert (Kp : forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e cx) - T_SEG_STK <= a < q_R (x_e cx)) ->
  ~ (q_pp (x_e cx) + rs_at_of sh ps <= a < q_pp (x_e cx) + rs_at_of sh ps + 4) ->
  ~ (q_R (x_e cx) + 0x100 <= a < q_R (x_e cx) + 0x108) ->
  ~ (rs_first ps = 1 /\ q_pp (x_e cx) + 0x400c <= a < q_pp (x_e cx) + 0x4014) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 H2 H3 H4. apply Hmem; [exact Ha | rewrite Hsp; exact H1 |]. intros [X|[X|X]]; auto. }
assert (Kc : forall a, q_R (x_e cx) <= a < q_R (x_e cx) + 0x100 \/ q_R (x_e cx) + 0x108 <= a < q_R (x_e cx) + 0x140 ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia; intros [_ X]; lia. }
(* ---- the cut LATCH ---- *)
change (cfg_at rsegs 0x82528 regs3 mem3 md3) with (cfg_at rsegs RS_LATCH regs3 mem3 md3).
apply (HL ly3 S3 W3 regs3 mem3 md3 sh np (ps ++ [(POD_PROP_PARAMS, PStruct es)]) r);
  [rewrite length_app, Hlen; cbn [length]; lia|].
split.
- split; [exact Hcore3|].
  split.
  { unfold rs_fsh_at in *. eapply rtm_fsh_kept; [exact Hfsh|]. intros j Hj.
    change (length rs_P0) with 56%nat in Hj.
    pose proof (Z.mul_div_le (q_F (x_e cx)) 8 ltac:(lia)) as D1.
    pose proof (Z.div_pos (q_F (x_e cx)) 8 ltac:(lia) ltac:(lia)) as D2.
    unfold shadow_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in PApp.
    apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia; intros [_ X]; lia. }
  split.
  { unfold rs_pp_at.
    change (rtm_bytes rsegs (w_H W3) mem3 (q_pp (x_e cx)) (pc_image (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None))).
    rewrite (w5_img_close_eq sh ps es Hsh7). fold len.
    assert (LB1 : length (overwrite (pc_buf (PbCut sh ps (Some es))) (Z.to_nat (rs_at_of sh ps))
        (le32 (len - rs_at_of sh ps - 8))) = length (pc_buf (PbCut sh ps (Some es)))).
    { apply length_overwrite. rewrite length_le32. lia. }
    assert (Nb : rtm_bytes rsegs (w_H W3) mem3 (q_pp (x_e cx)) (overwrite (pc_buf (PbCut sh ps (Some es)))
        (Z.to_nat (rs_at_of sh ps)) (le32 (len - rs_at_of sh ps - 8)))).
    { apply (rtm_bytes_patch rsegs (w_H W2) mem2); [exact (w5_img_buf _ _ _ _ _ _ _ _ _ Old) | | |].
      - rewrite Z2Nat.id by lia. exact Rsz.
      - rewrite length_le32. lia.
      - intros y Hy1 Hy2. rewrite length_le32 in Hy2. apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia;
        intros [_ X]; lia. }
    apply (w5_img_gen (w_H W2) mem2 (w_H W3) mem3 (q_pp (x_e cx)) (pc_buf (PbCut sh ps (Some es))) _ _
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
  cbn [rs_Rc rs_Rc0 rs_Kc rs_Hc rs_cur2 app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  all: first [ w5_kept Hat Hkeep Kc | (cbn [rt_at rt_xv]; rewrite Z.mod_small by lia; exact Rcur) ].
Qed.
End p.

Print Assumptions w5_piece_close.
