(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Step Frame Arr NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim StdioBase YajlBase YajlBuf YajlLex YajlParser.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanBudget AsanBudget2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_base B_alloc_iface B_iface B_live B_policy5 B_budget5 B_slack5 BI_shadow BI_iface BI_lowshadow BI_globals2 BYajlRep BYajl_iface BF_fakestack_rep BF_unwind BY_pot1 BY_pot2 BY_pot3 BY_acct_needs BY_client BYajl_asm B_bundle B_benv5 B_bframe B_bframe2 B_bframe3 B_bstack5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

Section InstY.
(* [comment removed for export] *)
Variable StdioRep : stdout_st -> mem -> Prop.
Variable RTMisc : aenv -> mem -> Prop.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
(* [comment removed for export] *)
Variable PL0 : fs_plumb.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Variable rt_fp : Z -> Prop.
Hypothesis RTMisc_agree : forall m m', RTMisc E0 m -> (forall a, rt_fp a -> m' (wa a) = m (wa a)) -> RTMisc E0 m'.
Hypothesis rt_fp_where : forall a, rt_fp a -> (0x10000 <= a < 0x603000 /\ ~ cl_cells a /\ ~ stdio_w a /\ ~ in_cells img_mut a) \/ rt_high2 E0 PL0 a.
Hypothesis RT_fsenv : forall m, RTMisc E0 m -> FSEnv bsegs E0 FSB0 PL0 m.
Hypothesis RT_icpg2 : forall m, RTMisc E0 m -> icp_globals2 bsegs m.
Variable so_fp : Z -> Prop.
Hypothesis StdioRep_agree : forall so m m', StdioRep so m -> (forall a, so_fp a -> m' (wa a) = m (wa a)) -> StdioRep so m'.
Hypothesis so_fp_where : forall a, so_fp a -> 0x10000 <= a < 0x603000 /\ ~ cl_cells a /\ ~ in_cells img_mut a.
(* [comment removed for export] *)
Variable mrel : Z -> aps -> Model -> option Z -> aps -> Model -> Prop.
Variable frel : Z -> aps -> Model -> aps -> Model -> Prop.
Variable rrel : Z -> Z -> aps -> Model -> option Z -> aps -> Model -> Prop.
#[local] Notation AHKc := (AHK StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (B_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (B_bundle.aN E0 FSB0 HR0).
#[local] Notation aEBc := (B_bundle.aEB EB0).
#[local] Notation uanchorc := (BF_unwind.uanchor bsegs).

Hypothesis W_malloc : amalloc_rz_stmt bsegs ACONSTS aps AHKc aps_so mrel aps_credit acharge uanchorc.
Hypothesis W_free : afree_rz_stmt bsegs ACONSTS aps AHKc aps_so frel aps_credit arefund uanchorc.
Hypothesis W_realloc : arealloc_rz_stmt bsegs ACONSTS aps AHKc aps_so rrel aps_credit acharge arefund uanchorc.
Hypothesis W_realloc0 : arealloc_null_rz_stmt bsegs ACONSTS aps AHKc aps_so rrel aps_credit acharge uanchorc.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition yF : Z := 1.
Definition phi_bufc : ybuf -> Z := BY_pot3.phi_buf acharge yF.
Definition phi_handc : yhandle -> Z -> Z := BY_pot3.phi_hand acharge arefund yF.
Definition phi_newc : Z -> Z := BY_pot3.phi_new acharge arefund yF.
Definition phrc : Z -> Z -> Z -> Z -> Z := BY_pot2.phr acharge arefund yF.
Lemma yF_ok : 0 <= yF <= 1. Proof. unfold yF; lia. Qed.
(* [comment removed for export] *)
Strategy 1000 [phi_bufc phi_handc phi_newc phrc BY_pot3.phi_buf BY_pot3.phi_hand BY_pot3.phi_new BY_pot3.G BY_pot2.phr BY_pot2.P].

Definition YP : ay_params :=
  mkAYP aps AHKc aps_so aSc aNc aEBc uanchorc ayR (aflagB E0 FSB0)
        aps_credit acharge arefund phi_bufc phi_handc phi_newc ycost yF.

Ltac yp_unfold := unfold YP in *; cbn [y_APS y_AHK y_SO y_aS y_aN y_aEB y_uanchor y_ayR y_aflag y_acredit y_acharge y_arefund y_phi_buf y_phi_hand y_phi_new y_cost y_free_cost] in *.

(* [comment removed for export] *)
#[local] Notation BF := (StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0) (only parsing).
Ltac inst lem := hnf; intros; yp_unfold; eapply lem; first [ eassumption | idtac "SUB-FAIL"; match goal with |- ?g => idtac g end ].
Lemma Y_kip : AHK_y_kip_stmt YP.
Proof.
  intros s LB LF m mo H. destruct (AHK_y_kip StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0 ENV0 s LB LF m mo H) as (A & B & C & D & E).
  yp_unfold. split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [| exact E].
  intros [w k] Hx. apply D. exact Hx.
Qed.
Lemma Y_blocks : AHK_y_blocks_stmt YP.
Proof. inst (AHK_blocks StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma Y_frame : AHK_y_frame_stmt YP.
Proof. inst (AHK_frame_y StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK rt_fp RTMisc_agree rt_fp_where so_fp StdioRep_agree so_fp_where). Qed.
Lemma Y_block_shadow : AHK_y_block_shadow_stmt YP.
Proof. inst (AHK_block_oshadow StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma Y_small_high : AHK_y_small_high_stmt YP.
Proof.
  hnf. intros s LB LF m mo b H Hb Hsz. yp_unfold. rewrite oshw_hi_0_47. unfold FS_SB.
  pose proof (AHK_y_small_high StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0 s LB LF m mo b H Hb Hsz) as [X _]. rewrite kHighMemBeg_val in X. exact X.
Qed.
Lemma Y_layout : AHK_y_layout_stmt YP.
Proof. inst (AHK_y_layout StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma Y_globals_shadow : AHK_y_globals_shadow_stmt YP.
Proof. inst (AHK_y_globals_shadow StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma Y_aflsep : AHK_y_aflsep_stmt YP.
Proof. inst (AHK_y_aflsep StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma Y_flag_cell : AHK_y_flag_cell_stmt YP.
Proof. inst (AHK_y_flag_cell StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma Y_fnodup : AHK_y_fnodup_stmt YP.
Proof. inst (AHK_y_fnodup StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma Y_fake_release : AHK_y_fake_release_stmt YP.
Proof. inst (AHK_fake_release StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK rt_fp RTMisc_agree rt_fp_where so_fp StdioRep_agree so_fp_where). Qed.

Lemma Y_mem_inv : AHK_y_mem_inv_stmt YP.
Proof. hnf. intros s LB LF m mo H. yp_unfold. exact (AHK_mem_inv _ _ _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma Y_perm : AHK_y_perm_stmt YP.
Proof. hnf. intros s LB LB' LF LF' m mo H P1 P2. yp_unfold. exact (AHK_perm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H P1 P2). Qed.
Lemma Y_statics : AHK_y_statics_stmt YP.
Proof. hnf. intros s LB LF m mo H. yp_unfold. exact (AHK_ay_statics _ _ _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma Y_ayR : AHK_y_ayR_stmt YP.
Proof. hnf. intros. yp_unfold. eapply AHK_ayR; eauto. Qed.
Lemma Y_ayR_refl : ayR_refl_stmt YP. Proof. exact ayR_refl. Qed.
Lemma Y_ayR_trans : ayR_trans_stmt YP. Proof. exact ayR_trans. Qed.

(* [comment removed for export] *)
Ltac pot_side := first [exact acharge_nonneg | exact arefund_nonneg | exact yF_ok | exact net256_big | assumption | lia].
Lemma Y_phi_shape : yphi_shape_stmt YP.
Proof. hnf; intros; yp_unfold. apply BY_pot3.phi_buf_shape. Qed.
Lemma Y_phi_first : yphi_first_stmt YP.
Proof. hnf; intros; yp_unfold. apply BY_pot3.phi_buf_first. Qed.
Lemma Y_phi_grow : yphi_grow_stmt YP.
Proof. hnf; intros; yp_unfold. apply BY_pot3.phi_buf_grow; pot_side. Qed.
Lemma Y_fb : forall b, y_free_cost YP + y_free_cost YP <= y_phi_buf YP b.
Proof. intros; yp_unfold. apply BY_pot3.phi_buf_2F; pot_side. Qed.
Lemma Y_hand_free : yphi_hand_free_stmt YP.
Proof. hnf; intros; yp_unfold. apply BY_pot3.phi_hand_free; pot_side. Qed.
Lemma Y_new_alloc : yphi_new_alloc_stmt YP.
Proof. hnf; intros; yp_unfold. apply BY_pot3.phi_new_alloc; pot_side. Qed.
Lemma Y_hand_split : yphi_hand_split_stmt YP phrc.
Proof.
  hnf; yp_unfold. unfold ypushc; yp_unfold. unfold phrc, phi_handc.
  pose proof acharge_nonneg as AC0. pose proof arefund_nonneg as AR0. pose proof yF_ok as HF. pose proof net256_big as BIG.
  split; [intros; apply BY_pot3.phi_hand_split|].
  split; [intros; apply BY_pot2.phr_nonneg; auto|].
  split; [intros; apply BY_pot2.phr_lex; auto|].
  split; [intros; apply BY_pot2.phr_pop; auto|].
  split; [intros; apply BY_pot2.phr_push; auto; lia|].
  split.
  - intros c c' u s L Hc Hcc Hs Hu. change YAJL_BS_INC with 128. split.
    + eapply BY_pot2.phr_realloc_liq; pot_side.
    + eapply BY_pot2.phr_realloc; pot_side.
  - intros; apply BY_pot2.phr_rest; auto.
Qed.
Lemma Y_acct_nonneg : yacct_nonneg_stmt YP.
Proof.
  hnf; yp_unfold. split; [exact acharge_nonneg|]. split; [| split].
  - intros b. apply BY_pot3.phi_buf_nonneg; pot_side.
  - intros h L. unfold phi_handc, BY_pot3.phi_hand, BY_pot3.phrc.
    pose proof (BY_pot3.phi_buf_nonneg acharge yF acharge_nonneg yF_ok (lx_buf (h_lexer h))).
    pose proof (BY_pot3.phi_buf_nonneg acharge yF acharge_nonneg yF_ok (h_decbuf h)).
    pose proof (BY_pot2.phr_nonneg acharge arefund yF acharge_nonneg yF_ok (h_bytesConsumed h) (h_used h) (h_stack_size h) L). lia.
  - intros L. apply BY_pot3.phi_new_nonneg; pot_side.
Qed.
Lemma Y_acct_free : yacct_free_stmt YP.
Proof. unfold yacct_free_stmt; yp_unfold. unfold yF; lia. Qed.
Lemma Y_hand_mono : yacct_hand_mono_stmt YP.
Proof.
  hnf; yp_unfold. intros h L L' HL. unfold phi_handc, BY_pot3.phi_hand, BY_pot3.phrc, BY_pot2.phr.
  assert (BY_pot2.PHI (h_bytesConsumed h) (h_used h) (h_stack_size h) L' <= BY_pot2.PHI (h_bytesConsumed h) (h_used h) (h_stack_size h) L)
    by (apply BY_pot2.PHI_mono; unfold BY_pot2.TT; lia).
  assert (BY_pot2.RSV acharge yF (h_bytesConsumed h) (h_stack_size h) L' <= BY_pot2.RSV acharge yF (h_bytesConsumed h) (h_stack_size h) L).
  { unfold BY_pot2.RSV. destruct (Z.ltb_spec (h_bytesConsumed h) L'); destruct (Z.ltb_spec (h_bytesConsumed h) L); try lia.
    pose proof (BY_pot2.ypc_nonneg acharge yF acharge_nonneg yF_ok (h_stack_size h)). lia. }
  lia.
Qed.
(* [comment removed for export] *)
Lemma phi_newc_val0 : phi_newc 0 = 5930618.
Proof. vm_compute. reflexivity. Qed.
Lemma phi_newc_lin : forall L, phi_newc L = phi_newc 0 + Z.max 0 L / 16.
Proof. intros L. unfold phi_newc, BY_pot3.phi_new. change (Z.max 0 0 / 16) with 0. lia. Qed.
Lemma Y_acct_new : yacct_new_stmt YP.
Proof. hnf; yp_unfold. intros L HL. rewrite phi_newc_lin, phi_newc_val0. unfold ycost. rewrite Z.max_r by lia. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section F.
Variable FS1 : Fs.Fs.
Variable FDS1 : list (word * FdEntry).
Variable M0 : mem.
(* [comment removed for export] *)
Definition img3 (a : Z) : Prop := c_seg3_lo ACONSTS <= a < c_seg3_hi ACONSTS \/ 0x6015a0 <= a < 0x6017c0.
Definition pin3 (m : mem) : Prop := forall a, img3 a -> m (wa a) = M0 (wa a).
Lemma seg3_vals : c_seg3_lo ACONSTS = 0xa5008 /\ c_seg3_hi ACONSTS = 0xa7000 /\ c_img_hi ACONSTS = 0x603000.
Proof. repeat split; reflexivity. Qed.

Lemma pin3_munch : forall W m m', pin3 m -> munch W m m' ->
  Forall (fun iv => (c_seg3_hi ACONSTS <= fst iv /\ (snd iv <= 0x6015a0 \/ 0x6017c0 <= fst iv)) \/ snd iv <= c_seg3_lo ACONSTS) W -> pin3 m'.
Proof.
  intros W m m' P MU FW a Ha. rewrite <- (P a Ha). apply MU. pose proof seg3_vals as (V1 & V2 & _).
  rewrite wa_unsigned by (unfold img3 in Ha; lia).
  unfold img3 in Ha. clear -FW Ha V1 V2. induction FW as [|[u v] W' Huv FW IH]; cbn; [exact I|]. cbn in Huv. split; [lia| exact IH].
Qed.

Lemma pin3_pres : forall LB LF SP m m', pin3 m -> aheap_pres bsegs ACONSTS LB LF SP m m' -> pin3 m'.
Proof.
  intros LB LF SP m m' P HP a Ha. rewrite <- (P a Ha). unfold img3 in Ha. pose proof seg3_vals as (V1 & V2 & _).
  apply (proj1 (HP a ltac:(lia) ltac:(right; right; right; unfold adrv_static; cbn [c_seg3_lo c_seg3_hi c_initialized c_ystat_lo c_ystat_hi ACONSTS] in *; lia))).
Qed.

Definition AHKF (s : aps) (LB : list ablock) (LF : list fblock) (m : mem) (mo : Model) : Prop :=
  AHKc s LB LF m mo /\ m_fs mo = FS1 /\ m_fds mo = FDS1 /\ pin3 m.
Definition ayRF (s : aps) (mo : Model) (s' : aps) (mo' : Model) : Prop :=
  ayR s mo s' mo' /\ m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo.

Definition YPF : ay_params :=
  mkAYP aps AHKF aps_so aSc aNc aEBc uanchorc ayRF (aflagB E0 FSB0)
        aps_credit acharge arefund phi_bufc phi_handc phi_newc ycost yF.

Ltac ypf_unfold := unfold YPF in *; cbn [y_APS y_AHK y_SO y_aS y_aN y_aEB y_uanchor y_ayR y_aflag y_acredit y_acharge y_arefund y_phi_buf y_phi_hand y_phi_new y_cost y_free_cost] in *.
(* [comment removed for export] *)
Ltac liftF lem := hnf; intros; ypf_unfold; match goal with H : AHKF _ _ _ _ _ |- _ => destruct H as (H & _ & _ & _); eapply lem; eauto end.

Lemma YF_kip : AHK_y_kip_stmt YPF.
Proof.
  intros s LB LF m mo (H & F1 & F2 & F3). destruct (Y_kip s LB LF m mo H) as (A & B & C & D & E). ypf_unfold. yp_unfold.
  split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|].
  intros mo' Hag HLI. destruct (E mo' Hag HLI) as [H' R']. pose proof (magree_frame _ _ Hag) as (Gfds & _ & _ & Gfs & _).
  split; [split; [exact H'| split; [congruence| split; [congruence| exact F3]]]| split; [exact R'| split; congruence]].
Qed.
Lemma YF_mem_inv : AHK_y_mem_inv_stmt YPF. Proof. liftF Y_mem_inv. Qed.
Lemma YF_perm : AHK_y_perm_stmt YPF.
Proof. intros s LB LB' LF LF' m mo (H & F1 & F2 & F3) P1 P2. split; [exact (Y_perm s LB LB' LF LF' m mo H P1 P2)| split; [exact F1| split; [exact F2| exact F3]]]. Qed.
Lemma YF_blocks : AHK_y_blocks_stmt YPF. Proof. liftF Y_blocks. Qed.

(* [comment removed for export] *)
Lemma ay_write_ok_above_seg3 : forall s LB LF m mo W, AHKc s LB LF m mo -> Forall (ay_write_ok LB LF) W ->
  Forall (fun iv => (c_seg3_hi ACONSTS <= fst iv /\ (snd iv <= 0x6015a0 \/ 0x6017c0 <= fst iv)) \/ snd iv <= c_seg3_lo ACONSTS) W.
Proof.
  intros s LB LF m mo W H FW.
  destruct (Y_blocks s LB LF m mo H) as (BR & _ & _). destruct (Y_layout s LB LF m mo H) as (LY & _ & _). yp_unfold.
  pose proof seg3_vals as (V1 & V2 & V3). pose proof alloc_ceiling_range as CR.
  apply Forall_forall. intros [u v] Hin. pose proof (proj1 (Forall_forall _ _) FW _ Hin) as WO. unfold ay_write_ok in WO. cbn in WO. cbn [fst snd].
  destruct WO as [WO|[(b & Hb & WO & _)|[(f & Hf & WO & _)|[(f & Hf & WO & _)|[WO WO2]]]]].
  - left. clear -WO CR V2. lia.
  - left. destruct (BR b Hb) as (_ & _ & _ & _ & IMG). clear -WO IMG V2 V3. lia.
  - left. destruct (LY f Hf) as (G1 & _). unfold amem in G1. clear -WO G1 V2. lia.
  - left. unfold oshw_lo, A_SB in WO. destruct (LY f Hf) as (G1 & _). unfold amem in G1. clear -WO G1 V2. Z.div_mod_to_equations. lia.
  - left. clear -WO WO2 V2. lia.
Qed.

Lemma YF_frame : AHK_y_frame_stmt YPF.
Proof.
  intros s LB LF m m' mo W (H & F1 & F2 & F3) MU WM FW. split; [exact (Y_frame s LB LF m m' mo W H MU WM FW)|]. split; [exact F1|]. split; [exact F2|].
  eapply pin3_munch; [exact F3| exact MU|]. ypf_unfold. exact (ay_write_ok_above_seg3 s LB LF m mo W H FW).
Qed.
Lemma YF_statics : AHK_y_statics_stmt YPF. Proof. liftF Y_statics. Qed.
Lemma YF_block_shadow : AHK_y_block_shadow_stmt YPF. Proof. liftF Y_block_shadow. Qed.
Lemma YF_small_high : AHK_y_small_high_stmt YPF. Proof. liftF Y_small_high. Qed.
Lemma YF_layout : AHK_y_layout_stmt YPF. Proof. liftF Y_layout. Qed.
Lemma YF_globals_shadow : AHK_y_globals_shadow_stmt YPF. Proof. liftF Y_globals_shadow. Qed.
Lemma YF_aflsep : AHK_y_aflsep_stmt YPF. Proof. liftF Y_aflsep. Qed.
Lemma YF_flag_cell : AHK_y_flag_cell_stmt YPF. Proof. liftF Y_flag_cell. Qed.
Lemma YF_fnodup : AHK_y_fnodup_stmt YPF. Proof. liftF Y_fnodup. Qed.
Lemma YF_fake_release : AHK_y_fake_release_stmt YPF.
Proof.
  intros s LB LF m m' mo N ff (H & F1 & F2 & F3) IN MU WM RC. split; [exact (Y_fake_release s LB LF m m' mo N ff H IN MU WM RC)|]. split; [exact F1|]. split; [exact F2|].
  eapply pin3_munch; [exact F3| exact MU|]. destruct (Y_layout s LB LF m mo H) as (LY & _ & _). destruct (LY _ IN) as (_ & _ & _ & _ & G5). cbn [fst snd] in G5.
  unfold amem in G5. ypf_unfold. yp_unfold. pose proof seg3_vals as (_ & V2 & _).
  constructor; [cbn [fst snd]; left; clear -G5 V2; lia| constructor].
Qed.
Lemma YF_ayR : AHK_y_ayR_stmt YPF.
Proof.
  intros s LB LF m mo s' LB' LF' m' mo' (H & F1 & F2 & _) (H' & F1' & F2' & _). ypf_unfold. split; [| split; congruence].
  eapply AHK_ayR; eauto.
Qed.
Lemma YF_ayR_refl : ayR_refl_stmt YPF. Proof. intros s mo. ypf_unfold. split; [apply ayR_refl| split; reflexivity]. Qed.
Lemma YF_ayR_trans : ayR_trans_stmt YPF.
Proof. intros s1 mo1 s2 mo2 s3 mo3 (A1 & A2 & A3) (B1 & B2 & B3). ypf_unfold. split; [eapply ayR_trans; eauto| split; congruence]. Qed.
Lemma YF_free1 : 1 <= y_free_cost YPF. Proof. ypf_unfold. unfold yF; lia. Qed.
Lemma YF_aref0 : forall n, 0 <= y_arefund YPF n. Proof. intros n. ypf_unfold. exact (arefund_nonneg n). Qed.
(* [comment removed for export] *)
Lemma YF_utriv : forall (URA : list Z) m SP ra s0, bv_unsigned s0 < alloc_ceiling -> In (bv_unsigned ra) URA -> y_uanchor YPF m SP ra s0.
Proof. intros URA m SP ra s0 H _. ypf_unfold. apply BF_unwind.ua_stop. left. exact H. Qed.
Lemma YF_ustep : forall (URA : list Z) m SP ra s0 ra' s0', In (bv_unsigned ra) URA -> SP + 16 <= bv_unsigned s0 < 2^47 ->
  rw_cells bsegs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> y_uanchor YPF m (bv_unsigned s0) ra' s0' -> y_uanchor YPF m SP ra s0.
Proof. intros URA m SP ra s0 ra' s0' _ [H1 H2] RC U. ypf_unfold. eapply BF_unwind.ua_step; eauto. Qed.
Lemma YF_uframe : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor YPF m SP ra s0 -> y_uanchor YPF m' SP ra s0.
Proof. intros m m' SP ra s0 AG U. ypf_unfold. eapply BF_unwind.uanchor_frame; eauto. Qed.
(* [comment removed for export] *)
Ltac reuse X stmt := pose proof X as XX; unfold stmt in XX |- *; ypf_unfold; yp_unfold; exact XX.
Lemma YF_phi_shape : yphi_shape_stmt YPF. Proof. reuse Y_phi_shape yphi_shape_stmt. Qed.
Lemma YF_phi_first : yphi_first_stmt YPF. Proof. reuse Y_phi_first yphi_first_stmt. Qed.
Lemma YF_phi_grow : yphi_grow_stmt YPF. Proof. reuse Y_phi_grow yphi_grow_stmt. Qed.
Lemma YF_fb : forall b, y_free_cost YPF + y_free_cost YPF <= y_phi_buf YPF b. Proof. pose proof Y_fb as XX. ypf_unfold. yp_unfold. exact XX. Qed.
Lemma YF_hand_free : yphi_hand_free_stmt YPF. Proof. reuse Y_hand_free yphi_hand_free_stmt. Qed.
Lemma YF_new_alloc : yphi_new_alloc_stmt YPF. Proof. reuse Y_new_alloc yphi_new_alloc_stmt. Qed.
Lemma YF_hand_split : yphi_hand_split_stmt YPF phrc. Proof. pose proof Y_hand_split as XX. unfold yphi_hand_split_stmt, ypushc in XX |- *. ypf_unfold. yp_unfold. exact XX. Qed.
Lemma YF_acct_nonneg : yacct_nonneg_stmt YPF. Proof. reuse Y_acct_nonneg yacct_nonneg_stmt. Qed.
Lemma YF_acct_free : yacct_free_stmt YPF. Proof. reuse Y_acct_free yacct_free_stmt. Qed.
Lemma YF_hand_mono : yacct_hand_mono_stmt YPF. Proof. reuse Y_hand_mono yacct_hand_mono_stmt. Qed.
Lemma YF_acct_new : yacct_new_stmt YPF. Proof. reuse Y_acct_new yacct_new_stmt. Qed.
(* [comment removed for export] *)
Lemma YF_icpg : forall s LB LF m mo, y_AHK YPF s LB LF m mo -> icp_globals bsegs m A_SB.
Proof. liftF (AHK_icp_globals StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma YF_icpg2 : forall s LB LF m mo, y_AHK YPF s LB LF m mo -> icp_globals2 bsegs m.
Proof.
  intros s LB LF m mo H. ypf_unfold. destruct H as (H & _ & _ & _). destruct (AHK_env _ _ _ _ _ _ _ _ _ _ _ _ _ H) as [EE _].
  apply RT_icpg2. rewrite <- EE. ahk_open H. exact Hrt.
Qed.
Lemma YF_lowsh : forall s LB LF m mo, y_AHK YPF s LB LF m mo -> low_shadow_ok m.
Proof. liftF (AHK_low_shadow StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma shw_hi_bound : forall A n, 1 <= n -> A + n <= alloc_ceiling -> shw_hi A_SB A n <= 0x10007fff8000.
Proof.
  intros A n Hn HA. pose proof alloc_ceiling_range as CR. unfold shw_hi. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (al8_le (A_SB + (A + n + -1) / 2^3)) as L. rewrite A_SB_val in L |- *. change (2^3) with 8 in L |- *.
  clear -Hn HA CR L. Z.div_mod_to_equations. lia.
Qed.
Lemma YF_icpb : forall s LB LF m mo b A n, y_AHK YPF s LB LF m mo -> In b LB ->
    ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    exists ws, shadow_window bsegs m A_SB A n ws /\ range_clean A_SB A n ws /\ shw_hi A_SB A n <= 0x10007fff8000 /\ amem (ab_addr b) (ab_size b).
Proof.
  intros s LB LF m mo b A n H Hb HA Hn HAn. ypf_unfold. destruct H as (H & _ & _ & _).
  destruct (AHK_icp_block_shadow StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0 s LB LF m mo b A n H Hb HA Hn HAn) as (ws & W1 & W2 & W3).
  destruct (AHK_blocks StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0 s LB LF m mo H) as (BR & _ & _). destruct (BR b Hb) as (_ & _ & _ & B4 & B5).
  exists ws. unfold A_SB, BI_iface.C_SB in *. split; [exact W1|]. split; [exact W2|]. split.
  - apply shw_hi_bound; [exact Hn| clear -HAn B4; lia].
  - unfold amem. unfold app_mem in W3. rewrite kHighMemBeg_val, kLowAppEnd_val in W3. cbn [c_img_hi ACONSTS] in B5. clear -W3 B5. lia.
Qed.
Lemma YF_icpr : forall s LB LF m mo b A n, y_AHK YPF s LB LF m mo -> In b LB -> ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    pages_budgeted (y_aS YPF s) (shw_lo A_SB A) (shw_hi A_SB A n).
Proof.
  intros s LB LF m mo b A n H Hb HA Hn HAn. ypf_unfold. destruct H as (H & _ & _ & _).
  destruct (AHK_icp_regions StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0 ENV0 s LB LF m mo H) as (_ & _ & _ & R4). exact (R4 b A n Hb HA Hn HAn).
Qed.
Lemma YF_ssh0 : forall s LB LF m mo A n, y_AHK YPF s LB LF m mo -> alloc_ceiling <= A -> 1 <= n -> A + n <= 2^47 ->
    exists ws, shadow_window bsegs m A_SB A n ws /\ range_clean A_SB A n ws
               /\ pages_budgeted (y_aS YPF s) (shw_lo A_SB A) (shw_hi A_SB A n) /\ ws = repeat (Z_to_bv 8 0) (length ws).
Proof.
  intros s LB LF m mo A n H HA Hn HAn. ypf_unfold. destruct H as (H & _ & _ & _).
  exact (AHK_icp_stack_shadow0 StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0 s LB LF m mo A n H HA Hn HAn).
Qed.

(* [comment removed for export] *)
Lemma liftF_malloc : forall (REL : Z -> aps -> Model -> option Z -> aps -> Model -> Prop),
  amalloc_rz_stmt bsegs ACONSTS aps AHKc aps_so REL aps_credit acharge uanchorc ->
  amalloc_rz_stmt bsegs ACONSTS aps AHKF aps_so REL aps_credit acharge uanchorc.
Proof.
  intros REL W. unfold amalloc_rz_stmt. intros until K. intros HK (H & F1 & F2 & F3) ST LOC LO AL SPH TP UA FRM A0 HN CR NB CONT.
  eapply (W ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB LF n lo K HK H); try eassumption.
  intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' mo' s' A ST' HP WM FRM' SO RL EFS EFD CR' EA BR AHK' J BS.
  eapply CONT; try eassumption.
  split; [exact AHK'| split; [congruence| split; [congruence| exact (pin3_pres _ _ _ _ _ F3 HP)]]].
Qed.
Lemma liftF_free : forall (REL : Z -> aps -> Model -> aps -> Model -> Prop),
  afree_rz_stmt bsegs ACONSTS aps AHKc aps_so REL aps_credit arefund uanchorc ->
  afree_rz_stmt bsegs ACONSTS aps AHKF aps_so REL aps_credit arefund uanchorc.
Proof.
  intros REL W. unfold afree_rz_stmt. intros until K. intros HK (H & F1 & F2 & F3) HA ST LOC LO AL SPH TP UA FRM A0 CF NB CONT.
  eapply (W ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB LF A lo K HK H); try eassumption.
  intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' mo' s' ST' HP FRM' SO AHK' RL EFS EFD CR'.
  eapply CONT; try eassumption. split; [exact AHK'| split; [congruence| split; [congruence| exact (pin3_pres _ _ _ _ _ F3 HP)]]].
Qed.
Lemma liftF_realloc : forall (REL : Z -> Z -> aps -> Model -> option Z -> aps -> Model -> Prop),
  arealloc_rz_stmt bsegs ACONSTS aps AHKc aps_so REL aps_credit acharge arefund uanchorc ->
  arealloc_rz_stmt bsegs ACONSTS aps AHKF aps_so REL aps_credit acharge arefund uanchorc.
Proof.
  intros REL W. unfold arealloc_rz_stmt. intros until K. intros HK (H & F1 & F2 & F3) HIN HB HL ST LOC LO AL SPH TP UA FRM A0 A1 HN CR NB CONT.
  eapply (W ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB LF A sz n lo old K HK H); try eassumption.
  intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' mo' s' A' ST' FRM' SO RL EFS EFD CR' EA BR AHK' CR2 HP J BS.
  eapply CONT; try eassumption. split; [exact AHK'| split; [congruence| split; [congruence| exact (pin3_pres _ _ _ _ _ F3 HP)]]].
Qed.
Lemma liftF_realloc_null : forall (REL : Z -> Z -> aps -> Model -> option Z -> aps -> Model -> Prop),
  arealloc_null_rz_stmt bsegs ACONSTS aps AHKc aps_so REL aps_credit acharge uanchorc ->
  arealloc_null_rz_stmt bsegs ACONSTS aps AHKF aps_so REL aps_credit acharge uanchorc.
Proof.
  intros REL W. unfold arealloc_null_rz_stmt. intros until K. intros HK (H & F1 & F2 & F3) ST LOC LO AL SPH TP UA FRM A0 A1 HN CR NB CONT.
  eapply (W ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB LF n lo K HK H); try eassumption.
  intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' mo' s' A ST' HP WM FRM' SO RL EFS EFD CR' EA BR AHK' J BS.
  eapply CONT; try eassumption. split; [exact AHK'| split; [congruence| split; [congruence| exact (pin3_pres _ _ _ _ _ F3 HP)]]].
Qed.

(* [comment removed for export] *)
Definition astack_mallocX (N ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : aps) (LB : list ablock) (LF : list fblock)
         (lo : Z) (K : TSet),
  K [] -> AHKc s LB LF m mo -> (ff_live_class LF N < 2)%nat ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK -> bv_unsigned sp <= 2^47 -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m -> tp = Z_to_bv 64 (c_tp ACONSTS) -> frm0 fc ->
  forall RR : Z, RR <= aps_credit s ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32)
          (m' : mem) (mo' : Model) (s' : aps) (ff : Z) (junk : list byte),
     stk bsegs m' lo (bv_unsigned sp) -> ay_pres LB LF (bv_unsigned sp) [] m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> frm0 fc' -> aps_so s' = aps_so s ->
     0 < ff -> ff mod ff_bytes N = 0 -> amem ff (ff_bytes N) -> ff + ff_bytes N <= alloc_ceiling ->
     (forall f, In f LF -> snd f + ff_bytes (fst f) <= ff \/ ff + ff_bytes N <= snd f) ->
     rw_cells bsegs m' ff [CB (Z.to_nat (ff_bytes N - 8)) junk; C8 (Z_to_bv 64 (aflagB E0 FSB0 N ff))] ->
     rw_cells bsegs m' (oshw_lo ff) [CB (Z.to_nat (Z.shiftl 8 N)) (repeat (Z_to_bv 8 0) (Z.to_nat (Z.shiftl 8 N)))] ->
     (exists fl, rw_cells bsegs m' (aflagB E0 FSB0 N ff) [C1 fl]) ->
     AHKc s' LB ((N, ff) :: LF) m' mo' -> ayR s mo s' mo' -> RR <= aps_credit s' ->
     (* [comment removed for export] *)
     m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo -> (forall a, 0 <= a < AY_IMG_HI -> m' (wa a) = m (wa a)) ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 ff) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                             F' (ret_pc ra) fc' None m' (seg_rom bsegs)) mo') K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 ENTRY) fc None m (seg_rom bsegs)) mo) K.

Lemma liftF_stack : forall N ENTRY, astack_mallocX N ENTRY -> astack_malloc_stmt YPF N ENTRY.
Proof.
  intros N ENTRY W. unfold astack_malloc_stmt. ypf_unfold. intros until K. intros HK (H & F1 & F2 & F3) FL ST LOC LO SPH AL MI TP FRM RR HRR CONT.
  eapply (W ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB LF lo K HK H); try eassumption.
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' mo' s' ff junk ST' AP WM MI' FRM' SO P1 P2 P3 P4 P5 C1 C2 C3 AHK' R' CR' EFS EFD IMG.
  eapply CONT; try eassumption.
  - split; [exact AHK'| split; [congruence| split; [congruence|]]].
    intros a Ha. rewrite <- (F3 a Ha). apply IMG. unfold img3 in Ha. pose proof seg3_vals as (V1 & V2 & _). unfold AY_IMG_HI. lia.
  - split; [exact R'| split; [exact EFS| exact EFD]].
Qed.
(* [comment removed for export] *)
Lemma SM1 : astack_mallocX 1 AY_STACK_MALLOC_1.
Proof. exact (astack_malloc1 StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK rt_fp RTMisc_agree rt_fp_where RT_fsenv so_fp StdioRep_agree so_fp_where). Qed.
Lemma SM0 : astack_mallocX 0 AY_STACK_MALLOC_0.
Proof. exact (astack_malloc0 StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK rt_fp RTMisc_agree rt_fp_where RT_fsenv so_fp StdioRep_agree so_fp_where). Qed.

(* [comment removed for export] *)
Theorem YF_fuzz : BYajl_iface.ayfuzz_stmt YPF.
Proof.
  exact (ayfuzz_closed YPF YF_kip YF_frame YF_blocks YF_mem_inv YF_block_shadow YF_small_high YF_layout YF_perm YF_statics YF_globals_shadow
           YF_aflsep YF_flag_cell YF_fnodup YF_fake_release YF_ayR YF_ayR_trans (liftF_stack 0 _ SM0) (liftF_stack 1 _ SM1)
           mrel frel rrel (liftF_malloc mrel W_malloc) (liftF_free frel W_free) (liftF_realloc rrel W_realloc) (liftF_realloc_null rrel W_realloc0)
           YF_aref0 YF_free1 AY_URA (fun pc H => H) (YF_utriv AY_URA) (YF_ustep AY_URA) YF_uframe
           YF_icpg YF_icpg2 YF_icpb YF_icpr YF_lowsh YF_ssh0
           YF_acct_nonneg YF_hand_mono YF_acct_free YF_acct_new YF_phi_shape YF_phi_grow YF_phi_first YF_fb YF_hand_free YF_new_alloc
           phrc YF_hand_split).
Qed.
End F.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Bridge.
(* [comment removed for export] *)

#[local] Notation wz := (fun z : Z => Z_to_bv 64 z).
#[local] Notation usp sp := (bv_unsigned sp).

Lemma zbytes_map_unsigned : forall (txt : list byte), zbytes (map bv_unsigned txt) = txt.
Proof. intros txt. unfold zbytes. rewrite map_map. rewrite <- (map_id txt) at 2. apply map_ext. intros b. exact (definitions.Z_to_bv_bv_unsigned 8%N b). Qed.
Lemma zlength_map_unsigned : forall (txt : list byte), zlength (map bv_unsigned txt) = Z.of_nat (length txt).
Proof. intros. unfold zlength. f_equal. clear. induction txt; cbn; congruence. Qed.

Ltac ypf_unfold := unfold YPF in *; cbn [y_APS y_AHK y_SO y_aS y_aN y_aEB y_uanchor y_ayR y_aflag y_acredit y_acharge y_arefund y_phi_buf y_phi_hand y_phi_new y_cost y_free_cost] in *.

(* [comment removed for export] *)
Lemma aheap_pres_of_Y : forall M0 LB SP m m', ay_pres LB [] SP [] m m' -> pin3 M0 m -> pin3 M0 m' -> aheap_pres bsegs ACONSTS LB [] SP m m'.
Proof.
  intros M0 LB SP m m' AP P0 P1 a Ha CL.
  assert (CASE : ay_client_addr LB [] SP a \/ img3 a).
  { destruct CL as [C|[C|[(f & Hf & _)|C]]]; [left; left; exact C| left; right; left; exact C| destruct Hf|].
    destruct C as [C|[C|[C|C]]]; cbn in C; [right; left; exact C| left; right; right; right; right; cbn; lia| left; right; right; right; left; cbn; lia
                                           | right; right; cbn; lia]. }
  destruct CASE as [C|C].
  - exact (AP a Ha C ltac:(cbn; tauto)).
  - pose proof (P1 a C) as E1. pose proof (P0 a C) as E0'. assert (E2 : m' (wa a) = m (wa a)) by congruence.
    split; [exact E2|]. unfold wview. rewrite E2. tauto.
Qed.

Theorem W_yfuzz : B_iface.ayfuzz_stmt bsegs ACONSTS aps AHKc aps_so ayfuzz_rel aps_credit uanchorc.
Proof.
  unfold B_iface.ayfuzz_stmt. intros until K. intros HK H BA LEN HN BLK NB ST LOC LO AL SPH TP GP UA FRM A0 A1 CR CONT.
  assert (HF : AHKF (m_fs mo) (m_fds mo) m s LB [] m mo) by (split; [exact H| split; [reflexivity| split; [reflexivity| intros a _; reflexivity]]]).
  pose proof (AHK_mem_inv _ _ _ _ _ _ _ _ _ _ _ _ _ H) as Hmi. pose proof (AHK_ay_statics _ _ _ _ _ _ _ _ _ _ _ _ _ H) as Hyst.
  pose proof (AHK_ay_cells _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (Y1 & Y2 & Y3).
  set (txt' := map bv_unsigned txt).
  assert (ZL : zlength txt' = n) by (subst txt'; rewrite zlength_map_unsigned; exact LEN).
  pose proof Y_blocks as YB. hnf in YB. yp_unfold. destruct (YB s LB [] m mo H) as (BR & _ & _).
  assert (TB : 0 < T /\ T + n < 2^62).
  { destruct BLK as [(b & Hb & B1 & B2)|[-> ->]]; [| cbn; lia].
    destruct (BR b Hb) as (R1 & _ & R3 & R4 & _). pose proof alloc_ceiling_range. lia. }
  assert (TX : text_at bsegs m T txt').
  { split; [subst txt'; rewrite zbytes_map_unsigned; exact BA|]. split; [| rewrite ZL; exact TB].
    subst txt'. apply Forall_map. apply Forall_forall. intros b _. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. cbn. lia. }
  assert (AY : AYST (YPF (m_fs mo) (m_fds mo) m) s LB [] m mo).
  { split; [exact HF|]. split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3| exact Hyst]. }
  assert (FP : ayframe_pre m sp tp fc lo AY_FUZZ_STACK).
  { split; [exact ST|]. split; [exact LOC|]. split; [clear -LO; unfold AYFUZZ_STACK in LO; replace AY_FUZZ_STACK with 9088 by (vm_compute; reflexivity); lia|].
    split; [exact SPH|]. split; [exact AL|]. split; [exact Hmi|]. split; [exact TP| exact FRM]. }
  pose proof (ycost_nonneg n ltac:(lia)) as YC0.
  (* [comment removed for export] *)
  pose proof Y_block_shadow as YBS. hnf in YBS. yp_unfold.
  assert (OTX : exists OT OTn, zlength txt' = 0 \/ (oshadow m OT OTn /\ OT <= T /\ T + zlength txt' <= OT + OTn /\ amem OT OTn /\ OT + OTn <= alloc_ceiling
                                                 /\ (exists bt, In bt LB /\ ab_addr bt <= OT /\ OT + OTn <= ab_addr bt + ab_size bt))).
  { destruct BLK as [(b & Hb & B1 & B2)|[N0 _]]; [| exists 0, 0; left; lia].
    destruct (Z.eq_dec n 0) as [->|NZ]; [exists 0, 0; left; exact ZL|].
    exists (ab_addr b), (ab_size b). right.
    destruct (YBS s LB [] m mo b H Hb ltac:(lia)) as [OS OH]. destruct (BR b Hb) as (R1 & _ & R3 & R4 & _).
    split; [exact OS|]. split; [lia|]. split; [lia|]. split; [exact OH|]. split; [exact R4|]. exists b. split; [exact Hb| lia]. }
  destruct OTX as (OT & OTn & OTX).
  eapply (YF_fuzz (m_fs mo) (m_fds mo) m [] LB T txt' OT OTn lo (aps_credit s - ycost n) K
            ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s AL HK AY TX).   (* [comment removed for export] *)
  - lia.
  - rewrite ZL. destruct BLK as [X|[X1 X2]]; [left; exact X| right; split; [exact X1| rewrite X2; reflexivity]].
  - exact OTX.
  - reflexivity.
  - reflexivity.
  - exact GP.
  - exact FP.
  - exact A0.
  - rewrite ZL. exact A1.
  - ypf_unfold. rewrite ZL. lia.
  - ypf_unfold. lia.
  - unfold AY_NBIG_REST. exact NB.
  - ypf_unfold. exact UA.
  - cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' mo' s' LK POST.
    destruct POST as (SO' & RF & CR' & (MI' & ST' & FRM' & _ & AP) & A0' & TX' & _ & LK0 & AY').
    subst LK. cbn [app] in AY'.
    destruct AY' as (HF' & Y1' & Y2' & Y3' & YST'). destruct HF' as (H' & F1' & F2' & P3'). destruct RF as ((RE & RB) & RFS & RFD). ypf_unfold.
    subst a0'. eapply CONT.
    + exact ST'.
    + eapply aheap_pres_of_Y; [exact AP| intros a _; reflexivity| exact P3'].
    + exact FRM'.
    + exact SO'.
    + exact H'.
    + apply ayfuzz_rel_intro; [split; [exact RE| exact RB]|]. pose proof (ycost_le_Ymax n ltac:(lia)) as YM. clear -CR' YM YC0. lia.
    + exact RFS.
    + exact RFD.
    + clear -CR'. lia.
Qed.
End Bridge.
End InstY.
End RC__1.
