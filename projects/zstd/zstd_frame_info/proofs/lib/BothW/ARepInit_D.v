(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoffBoth.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import MainExport MainFactsBoth MainEntryBoth.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import PrimaryShadow0.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase ABytes ALayout ARep AHeapP ARepInit_kit ARepInit_A.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section D.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok bsegs V m) both_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.   (* [comment removed for export] *)
  Hypothesis SH0 : bshadow0 V m.
  Let L := mkALayout (LV V) w U.

  #[using="rc HU"] Lemma sb_eq : al_space_beg L = 4096 * V 208%nat + -4096 * V 209%nat + 65536.
  Proof. unfold al_space_beg. cbn [al_V L LV Nat.eqb]. Local Ltac2 Set LiaHints.tbl := fun () => "0010>32017048862.12000004S2HU".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  #[using="rc HU"] Lemma sb_eq' : aspace_beg V = al_space_beg L.
  Proof. unfold aspace_beg. rewrite sb_eq. Local Ltac2 Set LiaHints.tbl := fun () => "0010>53350569272.12000004S2HU".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  #[using="HP HU HAT"] Lemma sb_facts : 0x10007fff8000 <= al_space_beg L /\ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP /\ al_space_beg L mod K_ALIGN = 0
                   /\ 0 <= al_space_beg L < 2^47.
  Proof. exact (alayout_space _ (alayout_ok_init V w U HP HU HAT)). Qed.

  (* [comment removed for export] *)
  #[using="rc HM HU"] Lemma ri_zero : forall i, 0 <= i < 4096 -> m (wa (al_space_beg L + K_SPACE_SIZE + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros i Hi. mf V m HM (MZero (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)) 4096) ZR.
    rewrite sb_eq. unfold K_SPACE_SIZE. Local Ltac2 Set LiaHints.tbl := fun () => "0020>21770839162.1562043009391.1500000400;S2HUS2HU2Hi".
replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37 + i)
      with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008 + i) by lia. apply ZR. lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  #[using="rc HM HU"] Lemma ri_wr : wr_at bsegs m (al_space_beg L + K_SPACE_SIZE) 4096.
  Proof.
    mwr V m HM (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)) 4096 W.
    rewrite sb_eq. unfold K_SPACE_SIZE. Local Ltac2 Set LiaHints.tbl := fun () => "0010>44672145423.13000004S2HU".
replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37)
      with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) by lia. exact W.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Ltac ri_cells c Hc :=
    apply zcells; [reflexivity
      | cbn [cells_size csize Nat.add]; intros i Hi; unfold aregion_info, ARI_STRIDE;
        match goal with |- m (wa ?x) = _ => replace x with (al_space_beg L + K_SPACE_SIZE + (x - (al_space_beg L + K_SPACE_SIZE))) by lia end;
        apply ri_zero; lia
      | unfold aregion_info, ARI_STRIDE; eapply wr_at_sub; [exact ri_wr| unfold K_SPACE_SIZE; lia| lia| cbn; lia] ].

  #[using="rc HM HP HU HAT"] Theorem aregion_cells_init : forall c, 1 <= c < K_NUM_CLASSES -> aregion_cells L (ST0 V) m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. pose proof sb_facts as (S1 & S2 & S3 & S4). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    unfold aregion_cells. rewrite get_cls_ST0. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user aclass0].
    Local Ltac2 Set LiaHints.tbl := fun () => "00E0>12506424771.2013503295158.2017460542521.1819391239118.2020253482943.1821512238092.1826275249356.1832865887692.1835198746510.2036775445311.1844123900145.184857126670.20 51604263052.1852832833114.185485029964.18 57623250188.1861566167217.1862102398975.1865901217422.2068121367679.187928892799.18 00000=00D00N00U00_00i01301=01D01N01X01_01i02302=02G02Q02[02b02l036S2HU2Hc2S12HiS2HU2HiS2HU2Hc2S1S2HU2HiS2HU2Hc2S1S2HU2Hc2S1S2HU2Hc2S1S2HU2Hc2S1S2HU2HiS2HU2Hc2S1S2HU2Hc2S1S2HU2HiS2HU2Hc2S1S2HU2Hc2S1S2HU2Hc2S1S2HU2Hc2S1S2HU2Hc2S1S2HU2Hc2S1S2HU2HiS2HU2Hc2S1S2HU2Hc2S1".
split; [ri_cells c Hc|]. split; [ri_cells c Hc|].
    split; [exists (repeat (Z_to_bv 8 0) 4); ri_cells c Hc|].
    split; [ri_cells c Hc|]. exists (repeat (Z_to_bv 8 0) 56); ri_cells c Hc.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rc U HU"] Lemma shad_add : forall a k, a mod 8 = 0 -> shad (a + k) = shad a + k / 8.
  Proof. intros a k Ha. unfold shad. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. nia. Qed.
  #[using="rc U HU"] Lemma shlen_eq : forall n, shlen n = n / 8.
  Proof. intros n. unfold shlen. Local Ltac2 Set LiaHints.tbl := fun () => "0010>29782367974.13000004S2HU".
rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="rc HP HU HAT"] Theorem afreearray_init : forall c, 1 <= c < K_NUM_CLASSES -> afreearray L (ST0 V) X0 m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. pose proof sb_facts as (S1 & S2 & S3 & S4). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    unfold afreearray. rewrite get_cls_ST0. cbn [c_num_freed c_mapped_free_array aclass0 x_cls X0 xc_free map].
    unfold afreearr, aregion, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296.
    Local Ltac2 Set LiaHints.tbl := fun () => "0050>23311011807.1828218526570.1729782367974.1845748428099.1763643767052.1800000?00L00P00Z00dS2HU2Hc2S12S21HS2HU2Hc2S12S3S2HUS2HU2Hc2S2S2HU2Hc2S1".
split; [apply u32arr_nil; lia|]. split.
    - exists []. rewrite Z.add_0_r. change (Z.to_nat (0 - 4 * 0)) with 0%nat. apply rw_cells_CB0; lia.
    - exists []. change (Z.to_nat (shlen 0)) with 0%nat. apply rw_cells_CB0; unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="rc HP HU HAT"] Theorem aslots_init : forall c, 1 <= c < K_NUM_CLASSES -> aslots L (ST0 V) X0 m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. pose proof sb_facts as (S1 & S2 & S3 & S4). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    unfold aslots. rewrite get_cls_ST0, ndist_ST0. cbn [c_allocated_user c_mapped_user aclass0]. Local Ltac2 Set LiaHints.tbl := fun () => "0030>11445810514.18329496297.18  59414757981.2000000?00I00PS2HU2Hc2S12S21HS2HU2Hc2S1S2HU2Hk".
split; [intros k Hk; lia|].
    exists []. unfold aregion, K_REGION. change (2^32) with 4294967296. rewrite Z.add_0_r. change (Z.to_nat (0 - 0)) with 0%nat. apply rw_cells_CB0; lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="rc HP HU HAT"] Theorem aslot_shadow_init : forall c, 1 <= c < K_NUM_CLASSES -> aslot_shadow L (ST0 V) X0 m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. pose proof sb_facts as (S1 & S2 & S3 & S4). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    unfold aslot_shadow. rewrite get_cls_ST0, ndist_ST0. cbn [c_allocated_user c_mapped_user aclass0]. Local Ltac2 Set LiaHints.tbl := fun () => "0040>28218526570.1729782367974.183351225609.20 45748428099.1700000=00A00H00RS2HU2Hc2S12S3S2HUS2HU2HkS2HU2Hc2S2".
split; [intros k Hk; lia|].
    unfold fill_at, aregion, K_REGION. change (2^32) with 4294967296. rewrite Z.add_0_r. change (Z.to_nat (shlen (0 - 0))) with 0%nat. cbn [repeat].
    apply rw_cells_CB0; unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rc HP HU HAT SH0"] Theorem ashadow_avail_init : forall c, 1 <= c < K_NUM_CLASSES -> ashadow_avail L (ST0 V) m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. pose proof sb_facts as (S1 & S2 & S3 & S4). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    destruct (primary_shadow0 V m SH0 HP) as [Z0' W0]. rewrite sb_eq' in Z0', W0.
    Local Ltac2 Set LiaHints.tbl := fun () => "00;0>12022228466.2012276081647.6 29782367974.2130821669680.2331811747424.5 33769611198.6 37262732865.204028188158.21 46033937187.2157414333782.2366103314940.2100000=00A00E00R00V00Z00g01101;01?01IS2HU2Hc2S12A8S2A8S2HUS2HU2Hc2S12HiS2S3S2A8S2HU2Hc2S12A8S2HU2Hc2S1S2HU2Hc2S1S2HUS2HU2Hc2S1".
assert (A8 : al_space_beg L mod 8 = 0) by (clear - S3; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    unfold ashadow_avail. rewrite get_cls_ST0. cbn [c_mapped_user c_mapped_free_array aclass0]. rewrite !Z.add_0_r, !Z.sub_0_r.
    unfold afreearr, aregion, K_REGION, K_FREEARR_OFF, K_FREEARR_MAX. change (2^32) with 4294967296.
    replace (shad (al_space_beg L + c * 4294967296 + 3758096384)) with (shad (al_space_beg L) + (c * 536870912 + 469762048))
      by (unfold shad; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - A8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    replace (shad (al_space_beg L + c * 4294967296)) with (shad (al_space_beg L) + c * 536870912)
      by (unfold shad; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - A8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    rewrite !shlen_eq. change (3758096384 / 8) with 469762048. change (536870912 / 8) with 67108864.
    split; split.
    - intros i Hi. replace (shad (al_space_beg L) + c * 536870912 + i) with (shad (al_space_beg L) + (c * 536870912 + i)) by lia. apply Z0'. lia.
    - eapply wr_at_sub; [exact W0| unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| lia| lia].
    - intros i Hi. replace (shad (al_space_beg L) + (c * 536870912 + 469762048) + i) with (shad (al_space_beg L) + (c * 536870912 + 469762048 + i)) by lia. apply Z0'. lia.
    - eapply wr_at_sub; [exact W0| unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| lia| lia].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End D.
End CANSEC1.
