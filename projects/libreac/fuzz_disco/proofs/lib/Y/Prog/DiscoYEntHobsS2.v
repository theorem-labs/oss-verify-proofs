(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 666 of its 732 lines of code are new or changed and 1212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntHobsS3.v; 552 of its 633 lines of code are new or changed and 651 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_frame_clean_len_c slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntClsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require RoleOf CheckTable CheckSighting.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntHobsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require HuntObsFacts HuntObsLib slot_hunt reac_hunt_observe_c slot_classify.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require ReacHuntObserve.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition hbs_acs : list YP09.chunk :=
  [YP09.mkChunk 368 (CVal 8 (SOff (AT_X + 32) 0)); YP09.mkChunk 408 (CVal 8 (SOff (AT_X + 33) 0))].

Lemma hbs_w64_add : forall a b, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Z.add_mod_idemp_l by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

Ltac hbs_ro HS bn :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let ix := idx_of_base rs bn in let ix := eval vm_compute in ix in
let rr := eval vm_compute in (nth ix rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx ix rr (set_window rr 0 0) HS
  ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ rr 0 0
     (st_ok_pi_region_nth Ex ssx msx ix rr HS ltac:(vm_compute; reflexivity))
     ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
Context {PO : PAObjImg lib_both3_0_listing}.
Context {PW : PAWinImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma hbs_env_old : forall cx E vals q, (q < AT_FL)%nat -> ew (d_env cx E vals) q = ew E q.
Proof. intros cx E vals q Hq. unfold d_env. apply ew_havoc_old. exact Hq. Qed.

Lemma hbs_env_x : forall cx E vals j q, q = (AT_X + j)%nat -> (j < length vals)%nat ->
  ew (d_env cx E vals) q = nth j vals (Z_to_bv 64 0).
Proof.
intros cx E vals j q -> Hj. unfold d_env. replace (AT_X + j)%nat with (AT_FL + S j)%nat by (unfold AT_X, AT_FL; lia).
rewrite (ew_havoc_new _ AT_FL _ (S j) (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis AIL : asink_img_laws SEGS B tfib_K.
Hypothesis KCAN : ak_canary tfib_K = FF_canary.
Hypothesis RHYP : d_ro_hyps B.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BSTEP : d_body_step_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.
Hypothesis BREAD : d_body_read_stmt B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis THOBS : ReacHuntObserve.treac_hunt_observe_spec B.

#[local] Notation DCTX := (d_ctx B MT XM_LIB RLO RHI tfib_K).

Lemma hbs_blocks_perm : forall cx h xb ly3 S3 ly2 S2,
  d_blocks B cx h xb ly3 S3 -> Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
  d_blocks B cx h xb ly2 S2.
Proof.
intros cx h xb ly3 S3 ly2 S2 (Hp & Hnin & Hbb & Hof) HP.
split; [exact (Permutation_trans HP Hp)|]. split; [exact Hnin|]. split; [|exact Hof].
rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HP), <- (blocks_bytes_bsum B ly3 S3). exact Hbb.
Qed.

Lemma hbs_frm_keep : forall cx nb fr len ly3 S3 (W3 : world SEGS) m3 md3 k3 W4 m4 lo hi (wr : Z -> Prop) h n shf,
  DCTX cx ly3 S3 W3 m3 md3 k3 -> d_body B cx h n (dxb fr len) shf ly3 S3 W3 m3 ->
  cl_kept B ly3 S3 W3 m3 W4 m4 lo hi wr -> (forall a, fr <= a < fr + len -> ~ wr a) ->
  d_frm cx nb fr len W3 m3 -> d_frm cx nb fr len W4 m4.
Proof.
intros cx nb fr len ly3 S3 W3 m3 md3 k3 W4 m4 lo hi wr h n shf HC3 HB HK Hnw (F1 & F2 & F3 & F4).
split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
destruct (Z.eq_dec fr 0) as [E0 | Hne].
- subst fr. rewrite (F2 eq_refl). intros j Hj. rewrite length_map, length_firstn in Hj. lia.
- pose proof HK as (_ & K2 & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & Hbl & _).
  assert (Hin : In (fr, len) (ablocks B ly3 S3)).
  { pose proof Hbl as (Hp & _). eapply Permutation_in; [apply Permutation_sym; exact Hp|].
    unfold dxb. replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). left; reflexivity. }
  pose proof (req_size_pos len ltac:(lia)) as Hrq.
  eapply YC88.garr8_aview_kept; [|exact F4]. intros a Ha. rewrite length_map in Ha.
  assert (Hl : Z.of_nat (length (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) <= len)
    by (rewrite length_firstn; lia).
  replace a with (fr + (a - fr)) by lia. apply (K2 fr len (a - fr) Hin); [lia|].
  replace (fr + (a - fr)) with a by lia. apply Hnw. lia.
Qed.

Lemma hbs_land : forall cx h i n now op nb fr len v r (fq : YK11.FPState) ly3 S3 (W : world SEGS) m md k acc
  ly2 S2 (W2 : world SEGS) (regs regs2 : bvmap 5 word) mem2 md2 H' lo (wr : Z -> Prop),
  DCTX cx ly3 S3 W m md k -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly2 S2 W2 mem2 md2 k ->
  frames S2 = frames S3 ->
  0 <= k <= EV_HEAD i + 1 -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 ->
  d_rL B cx regs -> getr regs 22 = w64 1 -> getr regs 26 = w64 now -> getr regs 23 = w64 v ->
  getr regs 1 = w64 (BASE + HB_P2) ->
  aregs_preserved regs regs2 -> getr regs2 10 = w64 r -> (r = -1 \/ r = 0 \/ r = 1) ->
  Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
  cl_kept B ly3 S3 W m W2 mem2 lo (d_A cx) wr ->
  (forall a, wr a -> (h <= a < h + HUNT_SIZE) \/ (d_obj cx OS <= a < d_obj cx OS + 24)) ->
  hb_X cx op nb fr len W m -> (v = -1 \/ v = 0 \/ v = 1 \/ v = 2) ->
  d_sp0 cx i now W m -> d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W m ->
  (0 < len -> (fr + len <= h \/ h + HUNT_SIZE <= fr) /\ (fr + len <= d_obj cx OS \/ d_obj cx OS + 24 <= fr)) ->
  garr8 SEGS (rd W2 mem2) h (map (fun b : byte => bv_unsigned b) H') -> hunt_ok H' ->
  firstn 6 (skipn 412 H') = our_of (c_pl cx) ->
  (0 <= r -> exists A, hb_sg cx nb fr len A W2 mem2 /\ (v = 1 -> s_role A <> 2)) ->
  hb_R2 B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len v r W2
    (mkCfg (mkst (fx := fq) regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
intros cx h i n now op nb fr len v r fq ly3 S3 W m md k acc ly2 S2 W2 regs regs2 mem2 md2 H' lo wr
  HC Hfrm0 HJ2 Hfrs2 Hk Hacc Hi Hn Hnow HrL R22 R26 R23 R1 HP2 Hr10 Hrr Hperm2 HK Hwr HX Hvr Hsp0 Hbody Hfrblk
  GH' HokH' HourH' Hsg.
pose proof HC as (Hbase & HJ & Hfrs).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m md k HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as HCL.
destruct (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof Hbody as (Tx & Gx & Lkx & Hx & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoffb &
  Hgeo & Hcan & Hstkd & Hawr).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
rewrite cl_fs6 in G2, G7, G8.
pose proof HX as (Hop & Hop2 & Hfrm & Hrec & Hopv & Hlennb & Hnbmax).
pose proof Hrec as (V200 & V328 & V368 & V408).
pose proof HrL as (Hspr & Hgpr & Htpr & H8r & H9r & H19r & H18r & H20r & H27r).
destruct (hb_hblk_read B MT XM_LIB RLO RHI tfib_K LAWS cx h n (dxb fr len) dsh_rec ly3 S3 W m md k 0
  HC Hbody ltac:(lia)) as (_ & _ & _ & _ & Hhmem & _).
pose proof HokH' as (LH' & _).
assert (Hwrc : forall a, wr a -> a < alloc_ceiling).
{ intros a Ha. destruct (Hwr a Ha) as [X | X]; unfold d_obj, DFRAME_SIZE in *; cbn [dobj_off] in *;
    unfold HUNT_SIZE in *; lia. }
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (HC2 : DCTX cx ly2 S2 W2 mem2 md2 k)
  by (split; [exact Hbase | split; [exact HJ2 | rewrite Hfrs2; exact Hfrs]]).
assert (Hfrng : forall a, (d_S cx - 104 <= a < d_S cx) \/ (d_A cx <= a < d_A cx + 472) \/
  (d_FB cx <= a < d_FB cx + 24) \/ (d_FB cx + 4088 <= a < d_FB cx + 4096) \/
  (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) m a).
{ intros a Ha.
  destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]].
  - apply K1; [unfold MFRAME, LLVMF_STK in *; lia | unfold MFRAME in HA1; lia |].
    intros Hw; pose proof (Hwrc a Hw); unfold MFRAME, LLVMF_STK in *; lia.
  - apply K1; [unfold MFRAME, LLVMF_STK in *; lia | lia |].
    intros Hw; pose proof (Hwrc a Hw); unfold MFRAME, LLVMF_STK in *; lia.
  - apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin);
      [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Efa, cl_fs6; lia|].
    intros Hw; destruct (Hwr a Hw) as [X | X]; clear - Ha X G7; unfold d_obj, HUNT_SIZE in *; cbn [dobj_off] in *; lia.
  - apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin);
      [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Efa, cl_fs6; lia|].
    intros Hw; destruct (Hwr a Hw) as [X | X]; clear - Ha X G7; unfold d_obj, HUNT_SIZE in *; cbn [dobj_off] in *; lia.
  - apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin);
      [right; unfold in_zr; cbn [fst snd]; rewrite Efa, cl_fs6; lia|].
    intros Hw. exfalso.
    assert (Hb : (d_FB cx <= a < d_FB cx + 4096) \/ (h <= a < h + HUNT_SIZE))
      by (destruct (Hwr a Hw) as [X | X]; [right; exact X | left; unfold d_obj in X; cbn [dobj_off] in X; lia]).
    clear Hw. revert Hb Ha Hhmem HF0 HFc HFia C1. clear.
    unfold shadow_addr, SHADOW_OFF, amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg,
      kHighMemEnd, ASAN_CEIL, HUNT_SIZE.
    intros. Z.div_mod_to_equations. lia. }
assert (Hframe2 : d_frame cx h dsh_rec W2 mem2)
  by exact (cl_frame_keep B MT XM_LIB RLO RHI tfib_K LAWS cx h dsh_rec W m ly2 S2 W2 mem2 md2 k
       HC2 Hframe Hfrng).
assert (Hshadow2 : d_shadow cx dsh_rec W2 mem2)
  by exact (cl_shadow_keep cx dsh_rec W W2 m mem2 Hshadow
       (fun a Ha => Hfrng a (or_intror (or_intror (or_intror (or_intror Ha)))))).
assert (Kobj : forall o, In o [OOUR; OT; OG; OLOCK] ->
  forall a, d_obj cx o <= a < d_obj cx o + dobj_size o ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) m a).
{ intros o Ho a Ha.
  assert (Hrng : d_FB cx + 2128 <= a < d_FB cx + 2972)
    by (cbv [In] in Ho; repeat (destruct Ho as [<-|Ho]; [unfold d_obj in Ha; cbn [dobj_off dobj_size] in Ha; lia|]);
        destruct Ho).
  apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin);
    [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Efa, cl_fs6; lia|].
  intros Hw; destruct (Hwr a Hw) as [X | X]; clear - Hrng X G7; unfold d_obj, HUNT_SIZE in *; cbn [dobj_off] in *; lia. }
pose proof Hobjs as (LT & GT & OKT & LG & GG & OKG & LLk & GLk & OKLk & GOur & LHH & GHH & OKHH & OURHH).
assert (Hobjs2 : d_objs cx h Tx Gx Lkx H' W2 mem2).
{ split; [exact LT|].
  split; [eapply YC88.garr8_aview_kept; [|exact GT]; intros a Ha; rewrite length_map, LT in Ha;
    apply (Kobj OT ltac:(cbv [In]; tauto)); cbn [dobj_size]; lia|].
  split; [exact OKT|]. split; [exact LG|].
  split; [eapply YC88.garr8_aview_kept; [|exact GG]; intros a Ha; rewrite length_map, LG in Ha;
    apply (Kobj OG ltac:(cbv [In]; tauto)); cbn [dobj_size]; lia|].
  split; [exact OKG|]. split; [exact LLk|].
  split; [eapply YC88.garr8_aview_kept; [|exact GLk]; intros a Ha; rewrite length_map, LLk in Ha;
    apply (Kobj OLOCK ltac:(cbv [In]; tauto)); cbn [dobj_size]; lia|].
  split; [exact OKLk|].
  split; [eapply YC88.garr8_aview_kept; [|exact GOur]; intros a Ha; rewrite length_map in Ha;
    unfold our_of in Ha; rewrite length_map, length_seq in Ha;
    apply (Kobj OOUR ltac:(cbv [In]; tauto)); cbn [dobj_size]; lia|].
  split; [exact LH'|]. split; [exact GH'|]. split; [exact HokH' | exact HourH']. }
assert (Hbody2 : d_body B cx h n (dxb fr len) dsh_rec ly2 S2 W2 mem2).
{ apply (BSTEP LAWS RHYP (conj AIL KCAN) cx h n (dxb fr len) (dxb fr len) dsh_rec dsh_rec ly3 S3 W m
    ly2 S2 W2 mem2 md2 k Tx Gx Lkx H' Hbody (conj Hbase HJ2)
    (hbs_blocks_perm cx h (dxb fr len) ly3 S3 ly2 S2 Hblocks Hperm2) Hobjs2).
  - intros a Hn0 Ha.
    pose proof Hbase as ((HPRE0 & _ & _ & _ & Hpn & _) & _).
    destruct Hpn as [(Hz & _) | (_ & Hpin)]; [lia|].
    pose proof Hblocks as (Hp & _).
    assert (Hpin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
      by (eapply Permutation_in; [apply Permutation_sym; exact Hp | apply in_or_app; right; right; exact Hpin]).
    pose proof (req_size_pos (c_n cx) ltac:(lia)).
    replace a with (c_p cx + (a - c_p cx)) by lia. apply (K2 (c_p cx) (c_n cx) (a - c_p cx) Hpin3); [lia|].
    replace (c_p cx + (a - c_p cx)) with a by lia.
    intros Hw; destruct (Hwr a Hw) as [X | X]; destruct (G8 Hn0) as (GP1 & GP2 & GP3 & GP4);
      clear - Ha X GP3 GP4; unfold d_obj, HUNT_SIZE in *; cbn [dobj_off] in *; lia.
  - intros a Hro Hos Her. apply K3; [exact (cl_roP_img a Hro) | exact Hos | exact Her].
  - exact Hframe2.
  - exact Hshadow2. }
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
assert (VM : forall off vv, 0 <= off -> off + 8 <= 472 ->
  val_mem SEGS (rd W m) (d_A cx + off) 8 vv -> val_mem SEGS (rd W2 mem2) (d_A cx + off) 8 vv)
  by (intros off vv Hoff1 Hoff2 Hv;
      exact (cl_slot_keep B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m md k W2 mem2 lo (d_A cx) wr off vv
        HC HK ltac:(lia) Hwrc Hoff1 Hoff2 Hv)).
assert (CS : forall (rz : Z) (rb : bv 5) (vv : word), rb = Z_to_bv 5 rz -> acallee_saved rz ->
  getr regs rb = vv -> getr regs2 rb = vv)
  by (intros rz rb vv -> Hrz Hvv; exact (cl_cs regs regs2 rz vv HP2 Hrz Hvv)).
unfold hb_R2, d_arm_at_pf, d_at.
exists fq, ly2, S2, regs2, mem2, md2, k, acc.
split; [rewrite R1; reflexivity|].
split; [exact Hfrm0|].
split; [exact Hbase|]. split; [exact HJ2|]. split; [rewrite Hfrs2; exact Hfrs|]. split; [exact Hk|].
split; [lia|]. split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ unfold d_rL, spZ in *.
  assert (E2 : getr regs2 2 = getr regs 2)
    by exact (cl_cs regs regs2 2 _ HP2 ltac:(unfold acallee_saved; lia) eq_refl).
  rewrite E2.
  split; [exact Hspr|].
  split; [exact (CS 3 3%bv _ eq_refl ltac:(unfold acallee_saved; lia) Hgpr)|].
  split; [exact (CS 4 4%bv _ eq_refl ltac:(unfold acallee_saved; lia) Htpr)|].
  split; [exact (CS 8 8%bv _ eq_refl ltac:(unfold acallee_saved; lia) H8r)|].
  split; [exact (CS 9 9%bv _ eq_refl ltac:(unfold acallee_saved; lia) H9r)|].
  split; [exact (CS 19 19%bv _ eq_refl ltac:(unfold acallee_saved; lia) H19r)|].
  split; [exact (CS 18 18%bv _ eq_refl ltac:(unfold acallee_saved; lia) H18r)|].
  split; [exact (CS 20 20%bv _ eq_refl ltac:(unfold acallee_saved; lia) H20r)|].
  exact (CS 27 27%bv _ eq_refl ltac:(unfold acallee_saved; lia) H27r). }
split.
{ split; [exact (CS 22 22%bv _ eq_refl ltac:(unfold acallee_saved; lia) R22)|].
  split; [exact (CS 26 26%bv _ eq_refl ltac:(unfold acallee_saved; lia) R26)|].
  split; [exact (CS 23 23%bv _ eq_refl ltac:(unfold acallee_saved; lia) R23) | exact Hr10]. }
split.
{ split.
  { split; [exact Hop|]. split; [exact Hop2|].
    split; [exact (hbs_frm_keep cx nb fr len ly3 S3 W m md k W2 mem2 lo (d_A cx) wr h n dsh_rec
      HC Hbody HK ltac:(intros a Ha Hw; destruct (Hfrblk ltac:(clear - Ha; lia)) as (Hd1 & Hd2);
        destruct (Hwr a Hw) as [X | X]; clear - Ha Hd1 Hd2 X; unfold d_obj, HUNT_SIZE in *; cbn [dobj_off] in *; lia)
      Hfrm)|].
    split; [split; [apply VM; [lia | lia | exact V200]|];
      split; [apply VM; [lia | lia | exact V328]|];
      split; [apply VM; [lia | lia | exact V368] | apply VM; [lia | lia | exact V408]]|].
    split; [destruct Hopv as (OP1 & OP2); split; apply VM; first [lia | assumption]|].
    split; [exact Hlennb | exact Hnbmax]. }
  split; [exact Hvr|]. split; [exact Hrr | exact Hsg]. }
split; [split; apply VM; first [lia | exact (proj1 Hsp0) | exact (proj2 Hsp0)] | exact Hbody2].
Qed.

Lemma hbs_model : forall (H FB O H' : list byte) len now out r (OUT : list byte -> Prop),
  hunt_ok H -> length FB = 50%nat -> hunt_ok H' -> out <> 0 ->
  ReacHuntObserve.tho_model H FB O len now out r H' OUT ->
  disco_table_c.sub H' 412 6 = disco_table_c.sub H 412 6 /\
  (0 <= r -> exists A, length A = 24%nat /\ OUT A /\
     reac_hunt_observe_c.ho_facts H FB (reac_frame_clean_len_model len) (disco_table_c.sub H 0 400) A).
Proof.
intros H FB O H' len now out r OUT HOK LFB HOK' Hout0 HM.
unfold ReacHuntObserve.tho_model in HM. cbv zeta in HM. destruct HM as [P1 P2].
set (L := reac_frame_clean_len_model len) in *.
pose proof HOK as (LH & TOK & _).
assert (HTe : disco_table_c.sub H 0 400 = firstn 400 H)
  by (unfold disco_table_c.sub; cbn [Z.to_nat skipn]; reflexivity).
assert (LT : length (disco_table_c.sub H 0 400) = 400%nat) by (rewrite HTe, length_firstn; lia).
assert (T1 : disco_table_c.tbl_T1 (disco_table_c.sub H 0 400))
  by (rewrite HTe; destruct TOK as (X & _); exact X).
assert (LLk12 : length (disco_table_c.sub H 400 12) = 12%nat) by (apply HuntObsLib.len_sub; lia).
assert (LLk : length (match disco_classify_c.cm_lock FB L (disco_table_c.sub H 412 6)
    (Some (disco_table_c.sub H 400 12)) with Some x => x | None => disco_table_c.sub H 400 12 end) = 12%nat)
  by (apply slot_hunt.lk_len; [exact LLk12 | intros _; exact LFB]).
assert (LG : length (disco_classify_c.sight FB L) = 24%nat) by exact (HuntObsFacts.sight_len FB L LFB).
destruct (Z.eq_dec (disco_classify_c.cm_ret FB L (disco_table_c.sub H 412 6)
  (Some (disco_table_c.sub H 400 12))) 0) as [C0 | C0].
- destruct (P2 C0) as (T' & c & OM & Er & EH & HA).
  pose proof (slot_hunt.obs_len _ _ _ _ _ _ LT LG T1 OM) as LT'.
  split.
  + rewrite EH. apply slot_hunt.sub412; [exact LT' | exact LLk |].
    rewrite firstn_app. rewrite HuntObsLib.len_sub by lia. replace (6 - 12)%nat with 0%nat by reflexivity.
    rewrite firstn_O, app_nil_r. unfold disco_table_c.sub. rewrite firstn_firstn. reflexivity.
  + intros Hr0. destruct (HA Hout0) as (A & HAns & HOUT & HF).
    exists A. split; [|split; [exact HOUT | exact HF]].
    assert (EF : firstn 400 H' = T').
    { rewrite EH, firstn_app, LT'. replace (400 - 400)%nat with 0%nat by reflexivity.
      rewrite firstn_O, app_nil_r. apply firstn_all2. lia. }
    pose proof HOK' as (_ & TOK' & _). rewrite EF in TOK'. destruct TOK' as (T1' & _).
    destruct HAns as (q & FRq & ->).
    destruct (q <? 0) eqn:Eq; [exact LG|].
    apply Z.ltb_ge in Eq. unfold disco_table_c.tbl_T1 in T1'.
    assert (Hq : 0 <= q < disco_table_c.n_of T') by (destruct FRq as [(X & _) | (X & _)]; lia).
    unfold reac_hunt_observe_c.ho_entry. rewrite !length_app, !HuntObsLib.len_sub by lia. reflexivity.
- destruct (P1 C0) as (Er & EH & _). split.
  + rewrite EH. apply slot_hunt.sub412; [exact LT | exact LLk | reflexivity].
  + intros Hr0. lia.
Qed.

Theorem hb_L2 : hb_L2_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold hb_L2_stmt. intros cx h i n now op nb fr len v W c Hin.
unfold hb_R1, d_arm_at_pf, d_at in Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & HrL & HRG0 & HXR & Hsp0 & Hbody).
destruct HRG0 as (R22 & R26 & R10 & R21).
destruct HXR as (HX & HROLE).
pose proof HX as (Hop & Hop2 & Hfrm & Hrec & Hopv & Hlennb & Hnbmax).
destruct HROLE as (Hvr & H0 & LH0 & GH0 & HROLEj).
pose proof Hbody as (T & G & Lk & HHc & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoffb & Hgeo & Hcan & Hstkd & Hawr).
assert (HC : DCTX cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as HCL.
destruct (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HArange : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
rewrite cl_fs6 in G2, G7, G8.
pose proof Hframe as (E & HdE & HRGs & HFL & V184 & V120 & V136 & V376 & V280 & V232 & V264).
pose proof Hrec as (V200 & V328 & V368 & V408).
pose proof Hfrm as (FR1 & FR2 & FR3 & FR4).
assert (Hfr64 : 0 <= fr < 2 ^ 64).
{ destruct (Z.eq_dec fr 0) as [->|Hne]; [lia|].
  pose proof Hblocks as (Hp & _).
  assert (Hinfr : In (fr, len) (ablocks B ly3 S3)).
  { eapply Permutation_in; [apply Permutation_sym; exact Hp|]. unfold dxb.
    replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). left; reflexivity. }
  destruct (al_blocks _ _ LAWS ly3 S3 W mem3 md3 fr len HAR Hinfr) as (_ & Hfr0 & Hfrc & _).
  pose proof (req_size_pos len ltac:(lia)). lia. }
assert (Hlen64 : 0 <= len < 2 ^ 64) by (unfold REC_MAX in FR1; lia).
assert (HACS : Forall (YP09.chunk_ok SEGS (d_env cx E (cl_vals regs [w64 fr; w64 len])) (rd W mem3) (d_A cx)) hbs_acs).
{ unfold hbs_acs. repeat apply Forall_cons; [| |apply Forall_nil].
  - apply (chunk_ok_val SEGS _ _ _ _ 8%N _ fr); [| cbn; lia | lia | exact V368].
    rewrite sv_denot_SOff0, (hbs_env_x cx E (cl_vals regs [w64 fr; w64 len]) 32%nat _ eq_refl
      ltac:(unfold cl_vals; rewrite length_app, length_map, length_seq; cbn [length]; lia)).
    unfold cl_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
    rewrite length_map, length_seq. cbn [Nat.sub nth]. reflexivity.
  - apply (chunk_ok_val SEGS _ _ _ _ 8%N _ len); [| cbn; lia | lia | exact V408].
    rewrite sv_denot_SOff0, (hbs_env_x cx E (cl_vals regs [w64 fr; w64 len]) 33%nat _ eq_refl
      ltac:(unfold cl_vals; rewrite length_app, length_map, length_seq; cbn [length]; lia)).
    unfold cl_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
    rewrite length_map, length_seq. cbn [Nat.sub nth]. reflexivity. }
pose proof (cl_regs_ok B cx E regs [w64 fr; w64 len] HdE HrL HArange) as HROK.
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E HB_P1 cl_sr
  (cl_vals regs [w64 fr; w64 len]) hbs_acs [] [] (d_facts [] [])
  HC HdE HRGs HFL HROK
  (FACTS LAWS cx ly3 S3 W mem3 md3 k E (cl_vals regs [w64 fr; w64 len]) [] [] HC HdE I I)
  HACS (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
hbs_ro HS 60%nat. hbs_ro HS 516%nat. hbs_ro HS 529%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E (cl_vals regs [w64 fr; w64 len]))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env.
  rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + HB_P1)) with (Z_to_bv 64 (BASE + HB_P1)).
paj_run_shc RUNP RUNC HS HJ.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Hpt := cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
assert (Hptr := cl_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
set (Ed := d_env cx E (cl_vals regs [w64 fr; w64 len])) in *.
assert (Hav : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a)
  by (intros a; apply aview_eq_of; apply Hptr).
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (HC4 : DCTX cx ly3 S3 W (ms_mem ms) md4 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k HC4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & HFpres4 & HSpres4 & HWpres4 & HAR4 & Hfin4 & Efa4 & Efl4).
assert (Hbody4 : d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms)).
{ apply (BRT cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 (ms_mem ms) (d_A cx) (d_A cx)
    (fun _ => False) Hbody).
  - unfold LLVMF_STK, MFRAME in *; lia.
  - unfold MFRAME in HA1; lia.
  - intros a [].
  - intros a _ _. exact (Hav a).
  - intros a _ (Hh1 & b & Hb). split; [exact Hh1|]. exists b. rewrite Hpt. exact Hb.
  - exact (cl_frame_keep B MT XM_LIB RLO RHI tfib_K LAWS cx h dsh_rec W mem3 ly3 S3 W (ms_mem ms) md4 k
      HC4 Hframe (fun a _ => Hav a)).
  - exact (cl_shadow_keep cx dsh_rec W W mem3 (ms_mem ms) Hshadow (fun a _ => Hav a)).
  - lia. }
pose proof Hbody4 as (Tx & Gx & Lkx & Hx & Hframe4 & Hshadow4 & Hobjs4 & Hblocks4 & Hinput4 & Himg4 & Hoffb4 &
  Hgeo4 & Hcan4 & Hstkd4 & Hawr4).
pose proof Hframe4 as (E4 & HdE4 & HRGs4 & HFL4 & _).
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS), (HROK r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
pose proof HrL as (Hspr & Hgpr & Htpr & H8r & H9r & H19r & H18r & H20r & H27r).
assert (Hsp4 : spZ (ms_regs ms) = d_A cx)
  by (unfold spZ; rewrite (RG 2%bv ltac:(cbv; tauto)); exact Hspr).
assert (Es0 : s0Z (ms_regs ms) = d_S cx).
{ unfold s0Z. rewrite (RG 8%bv ltac:(cbv; tauto)), H8r. unfold w64.
  apply unsigned_lit_small. unfold LLVMF_STK in *; lia. }
assert (Ed516 : ew Ed 516 = w64 (d_FB cx)).
{ subst Ed. rewrite hbs_env_old by (unfold AT_FL; lia). destruct HdE as (_ & _ & _ & _ & EF & _). exact EF. }
assert (R1 : getr (ms_regs ms) 1 = w64 (BASE + HB_P2)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let vv := eval vm_compute in (sr_get sr r) in
    change (sr_get sr r) with vv end.
  unfold w64, HB_P2. exact (codeptr_val _ 3608 HEI). }
assert (A10 : getr (ms_regs ms) 10 = w64 h).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS). rewrite <- R21, (HROK 21%bv).
  f_equal; vm_compute; reflexivity. }
assert (A11 : getr (ms_regs ms) 11 = w64 fr).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 11%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let vv := eval vm_compute in (sr_get sr r) in
    change (sr_get sr r) with vv end.
  rewrite sv_denot_SOff0.
  subst Ed. rewrite (hbs_env_x cx E (cl_vals regs [w64 fr; w64 len]) 32%nat 563%nat eq_refl
    ltac:(unfold cl_vals; rewrite length_app, length_map, length_seq; cbn [length]; lia)).
  unfold cl_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
  rewrite length_map, length_seq. cbn [Nat.sub nth]. reflexivity. }
assert (A12 : getr (ms_regs ms) 12 = w64 len).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 12%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let vv := eval vm_compute in (sr_get sr r) in
    change (sr_get sr r) with vv end.
  rewrite sv_denot_SOff0.
  subst Ed. rewrite (hbs_env_x cx E (cl_vals regs [w64 fr; w64 len]) 33%nat 564%nat eq_refl
    ltac:(unfold cl_vals; rewrite length_app, length_map, length_seq; cbn [length]; lia)).
  unfold cl_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
  rewrite length_map, length_seq. cbn [Nat.sub nth]. reflexivity. }
assert (A13 : getr (ms_regs ms) 13 = w64 now).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 13%bv HS). rewrite <- R26, (HROK 26%bv).
  f_equal; vm_compute; reflexivity. }
assert (A14 : getr (ms_regs ms) 14 = w64 (d_obj cx OS)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 14%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let vv := eval vm_compute in (sr_get sr r) in
    change (sr_get sr r) with vv end.
  cbn [sv_denot]. rewrite Ed516. unfold w64. rewrite hbs_w64_add. unfold d_obj. cbn [dobj_off]. reflexivity. }
assert (R23 : getr (ms_regs ms) 23 = w64 v).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 23%bv HS). rewrite <- R10, (HROK 10%bv).
  f_equal; vm_compute; reflexivity. }
destruct (cl_achain B MT XM_LIB XN_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md4 k E4 (d_A cx)
  HC4 HdE4 (Forall_inv HRGs4) ltac:(unfold MFRAME in HA1; lia)) as (ch & Hch).
assert (ESTK : ReacHuntObserve.REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
assert (EDEP : ReacHuntObserve.REAC_HUNT_OBSERVE_DEPTH = 7) by reflexivity.
destruct (hb_hblk_read B MT XM_LIB RLO RHI tfib_K LAWS cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms) md4 k
  8688 HC4 Hbody4 ltac:(lia))
  as (Hhin & Hh0 & Hh8 & Hh63 & Hhmem & Hhra & Hhsh & Hhoff & Hhstk & Hhfb & Hhpres).
destruct (hb_obj_read B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k OS 8688
  HC4 Hshadow4 ltac:(vm_compute; reflexivity) ltac:(lia))
  as (Ho0 & Ho63 & Ho8 & Homem & Hora & Hosh & Hooff & Hostk & Hopres).
cbn [dobj_size] in Ho63, Homem, Hora, Hosh, Hooff, Hostk, Hopres.
destruct (cl_garr8_ex (w_H W) (ms_mem ms) (d_obj cx OS) 24 ltac:(intros a Ha; apply Hopres; lia))
  as (O & LO & GO).
assert (LFR : length (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)) = Z.to_nat len)
  by (apply cl_rest_len; lia).
pose proof (slot_classify.fb50_len (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) as LFB.
destruct (BREAD cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms) Hbody4) as (_ & _ & _ & HRDH).
assert (GH0' : garr8 SEGS (rd W (ms_mem ms)) h (map (fun b : byte => bv_unsigned b) H0)).
{ eapply YC88.garr8_aview_kept; [|exact GH0]. intros a _. exact (Hav a). }
destruct (HRDH H0 LH0 GH0') as (HokH0 & HourH0).
assert (GFR4 : garr8 SEGS (rd W (ms_mem ms)) fr
  (map (fun b : byte => bv_unsigned b) (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)))).
{ eapply YC88.garr8_aview_kept; [|exact FR4]. intros a _. exact (Hav a). }
assert (Hfrm4 : d_frm cx nb fr len W (ms_mem ms))
  by (split; [exact FR1|]; split; [exact FR2|]; split; [exact FR3 | exact GFR4]).
assert (Hfrblk : 0 < len -> In (fr, len) (ablocks B ly3 S3) /\ 0 < fr /\
  (fr + req_size len <= h \/ h + req_size HUNT_SIZE <= fr) /\
  (fr + req_size len <= d_FB cx \/ d_FB cx + 4096 <= fr)).
{ intros Hl0.
  destruct (hb_blk_read B MT XM_LIB RLO RHI tfib_K LAWS cx h n dsh_rec nb fr len ly3 S3 W (ms_mem ms) md4 k
    8688 HC4 Hbody4 Hfrm4 Hlennb Hl0 ltac:(lia))
    as (Hfin2 & Hf0 & Hf63 & Hfmem & Hfra & Hfsh & Hfoff & Hfstk & Hffb & Hfpres).
  assert (Hne : fr <> 0) by lia.
  pose proof Hblocks4 as (Hp & _).
  assert (Hperm2 : Permutation (ablocks B ly3 S3)
    ((fr, len) :: (h, HUNT_SIZE) :: ablocks B (c_ly cx) (c_S cx))).
  { eapply Permutation_trans; [exact Hp|]. unfold dxb.
    replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). apply Permutation_refl. }
  pose proof (sep_blocks_perm SEGS B LAWS ly3 S3 W (ms_mem ms) md4 (fr, len) (h, HUNT_SIZE)
    (ablocks B (c_ly cx) (c_S cx)) HAR4 Hperm2) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
  split; [exact Hfin2|]. split; [exact Hf0|]. split; [lia | exact Hffb]. }
assert (HrL4 : d_rL B cx (ms_regs ms)).
{ unfold d_rL, spZ in *. rewrite !RG by (cbv; tauto). repeat split; assumption. }
assert (R22m : getr (ms_regs ms) 22 = w64 1) by (rewrite (RG 22%bv ltac:(cbv; tauto)); exact R22).
assert (R26m : getr (ms_regs ms) 26 = w64 now) by (rewrite (RG 26%bv ltac:(cbv; tauto)); exact R26).
assert (VM0 : forall a vv, val_mem SEGS (rd W mem3) a 8 vv -> val_mem SEGS (rd W (ms_mem ms)) a 8 vv)
  by (intros a vv Hv; eapply YC88.val_mem_aview_kept_x; [|exact Hv]; intros x _; exact (Hav x)).
assert (HX4 : hb_X cx op nb fr len W (ms_mem ms)).
{ split; [exact Hop|]. split; [exact Hop2|]. split; [exact Hfrm4|].
  split; [split; [apply VM0; exact V200|]; split; [apply VM0; exact V328|];
    split; [apply VM0; exact V368 | apply VM0; exact V408]|].
  split; [destruct Hopv as (OP1 & OP2); split; apply VM0; assumption|].
  split; [exact Hlennb | exact Hnbmax]. }
assert (Hsp04 : d_sp0 cx i now W (ms_mem ms))
  by (split; apply VM0; [exact (proj1 Hsp0) | exact (proj2 Hsp0)]).
destruct (DCRO LAWS RHYP ly3 S3 W (ms_mem ms) md4 HAR4 Himg4) as (_ & _ & _ & _ & (HKM & HKT & _) & _).
pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Hms.
rewrite (pa_sigma_reac_hunt_observe (PI := PI)) in Hms. cbn [ss_pc setpc] in Hms.
rewrite Hms.
eapply SRr_bind.
{ apply (THOBS fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md4 k (ms_regs ms) ch h fr len now (d_obj cx OS)
    h HUNT_SIZE H0 (slot_classify.fb50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) O HJ Himg4).
  - rewrite R1. apply ret_ok_codeptr_v; [unfold HB_P2; lia | unfold HB_P2; reflexivity].
  - unfold raZ. rewrite R1. unfold w64. pose proof (@pa_B_ok _ _ PI) as (HB0 & HB1 & _).
    rewrite unsigned_lit_small by (unfold HB_P2; lia).
    pose proof (pa_base_lo (PI := PI)). unfold IMG_LO in *. unfold HB_P2. lia.
  - rewrite (RG 3%bv ltac:(cbv; tauto)). exact Hgpr.
  - rewrite (RG 4%bv ltac:(cbv; tauto)). exact Htpr.
  - rewrite Hsp4, Es0. exact Hch.
  - rewrite Hsp4. unfold MFRAME, LLVMF_STK in *. lia.
  - rewrite Hsp4, ESTK. unfold LLVMF_STK, MFRAME in *. lia.
  - rewrite Hsp4. unfold MFRAME, LLVMF_STK in *. lia.
  - rewrite Hfrs, EDEP. cbn [length]. lia.
  - exact A10.
  - exact A11.
  - exact A12.
  - exact A13.
  - exact A14.
  - exact Hlen64.
  - exact Hnow.
  - lia.
  - exact Hh0.
  - exact Hh8.
  - exact Hhin.
  - lia.
  - pose proof (req_size_pos HUNT_SIZE ltac:(unfold HUNT_SIZE; lia)). unfold HUNT_SIZE in *. lia.
  - intros a Ha. pose proof Hblocks4 as (_ & Hnin & _).
    pose proof (req_size_pos HUNT_SIZE ltac:(unfold HUNT_SIZE; lia)) as Hrq.
    right; right; left. exists h, HUNT_SIZE. split; [exact Hhin|].
    split; [exact (Forall_inv Hnin) | unfold HUNT_SIZE in *; lia].
  - exact HokH0.
  - exact GH0'.
  - exact LFB.
  - intros H50. destruct (Hfrblk ltac:(lia)) as (Hfin2 & Hf0 & Hdh & Hdf).
    pose proof (req_size_pos len ltac:(lia)) as Hrq1.
    pose proof (req_size_pos HUNT_SIZE ltac:(unfold HUNT_SIZE; lia)) as Hrq2.
    split; [exact Hf0|].
    split; [exists fr, len; split; [exact Hfin2 | lia]|].
    split; [clear - H50 Hdh Hrq1 Hrq2; unfold HUNT_SIZE in *; lia|].
    rewrite cl_fb50 by (rewrite LFR; lia). apply cl_garr8_firstn. exact GFR4.
  - intros _. split; [|split].
    + unfold ReacHuntObserve.tho_out.
      split; [exact Ho8|]. split; [exact Ho63|]. split; [exact Homem|].
      split; [right; rewrite Hsp4, ESTK; lia|].
      split; [left; exists DFRAME_CLASS, (c_fpos cx); split; [exact Hfin|];
        rewrite Efa, cl_fs6; unfold d_obj; cbn [dobj_off]; lia|].
      split; [exact Hora|]. split; [exact Hosh|].
      split; [intros a Ha; exact (Hawr4 a ltac:(unfold d_obj in Ha; cbn [dobj_off] in Ha; unfold DFRAME_SIZE; lia))|].
      split; [exact LO|]. split; [exact GO|].
      left. exists DFRAME_CLASS, (c_fpos cx). split; [exact Hfin|].
      rewrite Efa, cl_fs6. unfold d_obj. cbn [dobj_off]. lia.
    + unfold d_obj. cbn [dobj_off]. unfold HUNT_SIZE in *. lia.
    + intros H50. destruct (Hfrblk ltac:(lia)) as (_ & _ & _ & Hdf).
      pose proof (req_size_pos len ltac:(lia)). unfold d_obj. cbn [dobj_off]. lia.
  - exact HKM.
  - exact HKT. }
intros W2 c2 _ Hpost.
apply SRr_ret.
destruct Hpost as (fx2 & ly2 & S2 & regs2 & mem2 & md2 & r & H' & Hc2 & _ & Hcsr2 & HJ2 & HP2 & Hr10 & Hfrs2 & Hperm2 & HK &
  GH' & HokH' & Hrr & HM).
destruct (hbs_model H0 (slot_classify.fb50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) O H' len now
  (d_obj cx OS) r _ HokH0 LFB HokH' ltac:(lia) HM) as (EsubH' & HAex).
exists r. rewrite Hc2.
apply (hbs_land cx h i n now op nb fr len v r fx2 ly3 S3 W (ms_mem ms) md4 k acc ly2 S2 W2 (ms_regs ms) regs2
  mem2 md2 H' (d_A cx - 8688) (ReacHuntObserve.tho_wr h (d_obj cx OS)) HC4 (hb_frm0_post fq fx2 Hfrm0 Hcsr2) HJ2
  Hfrs2 Hk Hacc Hi Hn Hnow HrL4 R22m R26m R23 R1 HP2 Hr10 Hrr Hperm2).
- rewrite <- Hsp4, <- ESTK. exact HK.
- intros a [X | (_ & X)]; [left; unfold HUNT_SIZE; exact X | right; exact X].
- exact HX4.
- exact Hvr.
- exact Hsp04.
- exact Hbody4.
- intros Hl0. destruct (Hfrblk Hl0) as (_ & _ & Hdh & Hdf).
  pose proof (req_size_pos len ltac:(clear - Hl0; lia)) as Q1.
  pose proof (req_size_pos HUNT_SIZE ltac:(unfold HUNT_SIZE; lia)) as Q2.
  unfold d_obj. cbn [dobj_off]. clear - Hl0 Hdh Hdf Q1 Q2. unfold HUNT_SIZE in *. split; lia.
- exact GH'.
- exact HokH'.
- change (firstn 6 (skipn 412 H')) with (disco_table_c.sub H' 412 6). rewrite EsubH'. exact HourH0.
- intros Hr0. destruct (HAex Hr0) as (A & LA & GA & HF).
  pose proof HF as (HL50 & HSM & _ & _ & _ & _ & _ & _ & HRL).
  assert (Hlen50 : 50 <= len).
  { revert HL50. unfold reac_frame_clean_len_model.
    destruct ((54 <=? len) && ((len - 52) mod 36 =? 2)); intros; lia. }
  assert (EFB : slot_classify.fb50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)) =
    firstn 50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) by (apply cl_fb50; rewrite LFR; lia).
  exists A. split.
  + split; [exact LA|]. split; [exact GA|].
    pose proof (slot_hunt.ho_sf H0 _ _ _ A (our_of (c_pl cx)) LA ltac:(rewrite LFB; lia) HourH0 HF) as HSF.
    rewrite EFB in HSF. set (X := firstn (Z.to_nat len) (rest_of (c_pl cx) nb)) in *.
    rewrite firstn_firstn in HSF. exact HSF.
  + intros Ev E2. destruct (HROLEj Ev) as (j & Hj1 & Hj2 & Hj3).
    assert (Emac : hb_mac cx nb fr len = s_mac A).
    { rewrite HSM, EFB. unfold hb_mac. replace (11 <? len) with true by (symmetry; apply Z.ltb_lt; lia).
      set (X := firstn (Z.to_nat len) (rest_of (c_pl cx) nb)).
      unfold disco_table_c.sub. change (Z.to_nat 6) with 6%nat.
      rewrite skipn_firstn_comm, firstn_firstn. reflexivity. }
    rewrite (HRL (ex_intro _ j (conj Hj1 (conj (eq_trans Hj2 Emac) Hj3)))) in E2. discriminate.
Qed.
End h.
End f.
End d.
