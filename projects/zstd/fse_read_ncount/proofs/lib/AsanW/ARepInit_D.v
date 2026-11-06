(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoff.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import MainExport MainFactsAsan MainEntry PrimaryShadow0.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase ABytes ALayout ARep AHeapP ARepInit_kit ARepInit_A.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Section D.
Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.
Hypothesis SH0 : ashadow0 V m.
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
#[using="rc HM HU"] Lemma ri_zero : forall i, 0 <= i < 4096 -> m (wa (al_space_beg L + K_SPACE_SIZE + i)) = Some (Z_to_bv 8 0).
Proof.
intros i Hi. mf V m HM (MZero (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)) 4096) ZR.
rewrite sb_eq. unfold K_SPACE_SIZE. Local Ltac2 Set LiaHints.tbl := fun () => "0020>21770839162.1562043009391.1500000400;S2HUS2HU2Hi".
replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37 + i)
with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008 + i) by lia. apply ZR. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc HM HU"] Lemma ri_wr : wr_at asegs m (al_space_beg L + K_SPACE_SIZE) 4096.
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
#[using="rc U HU"] Lemma shlen_eq : forall n, shlen n = n / 8.
Proof. intros n. unfold shlen. Local Ltac2 Set LiaHints.tbl := fun () => "0010>29782367974.13000004S2HU".
rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc HP HU HAT"] Theorem afreearray_init : forall c, 1 <= c < K_NUM_CLASSES -> afreearray L (ST0 V) X0 m c.
Proof.
intros c Hc. unfold K_NUM_CLASSES in Hc. pose proof sb_facts as (S1 & S2 & S3 & S4). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
unfold afreearray. rewrite get_cls_ST0. cbn [c_num_freed c_mapped_free_array aclass0 x_cls X0 xc_free map].
unfold afreearr, aregion, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>23311011807.1825606867439.3225916321876.3229782367974.1863643767052.1800000?00T00f00j014S2HU2Hc2S12S21HS2HU2Hc2S12S31H2H02H4S2HU2Hc2S21H2H02H9S2HUS2HU2Hc2S1".
split; [apply u32arr_nil; lia|]. split.
- exists []. rewrite Z.add_0_r. change (Z.to_nat (0 - 4 * 0)) with 0%nat. apply rw_cells_CB0; lia.
- exists []. change (Z.to_nat (shlen 0)) with 0%nat. apply rw_cells_CB0; unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia.
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
unfold aslot_shadow. rewrite get_cls_ST0, ndist_ST0. cbn [c_allocated_user c_mapped_user aclass0]. Local Ltac2 Set LiaHints.tbl := fun () => "0040>25606867439.3225916321876.3229782367974.183351225609.20 00000E00W00[00bS2HU2Hc2S12S31H2H02H4S2HU2Hc2S21H2H02H9S2HUS2HU2Hk".
split; [intros k Hk; lia|].
unfold fill_at, aregion, K_REGION. change (2^32) with 4294967296. rewrite Z.add_0_r. change (Z.to_nat (shlen (0 - 0))) with 0%nat. cbn [repeat].
apply rw_cells_CB0; unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc HP HU HAT SH0"] Theorem ashadow_avail_init : forall c, 1 <= c < K_NUM_CLASSES -> ashadow_avail L (ST0 V) m c.
Proof.
intros c Hc. unfold K_NUM_CLASSES in Hc. pose proof sb_facts as (S1 & S2 & S3 & S4). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
destruct (primary_shadow0 V m SH0 HP) as [Z0' W0]. rewrite sb_eq' in Z0', W0.
Local Ltac2 Set LiaHints.tbl := fun () => "00;0>29782367974.2130821669680.2337247894447.354028188158.21 43817563406.2046033937187.2157414333782.2366103314940.2166151427842.198341429490.35 9609688955.20 00000400A00P00Z00f01001401>01J01Y01eS2HUS2HU2Hc2S12HiS2HU2Hc2S12A81HS2HU2Hc2S1S2A81H2H42H5S2HU2Hc2S1S2HUS2HU2Hc2S1S2S31H2H02H4S2HU2Hc2S12A81HS2A81H2H42H5".
assert (A8 : al_space_beg L mod 8 = 0) by (clear - S3; Z.div_mod_to_equations; lia).
unfold ashadow_avail. rewrite get_cls_ST0. cbn [c_mapped_user c_mapped_free_array aclass0]. rewrite !Z.add_0_r, !Z.sub_0_r.
unfold afreearr, aregion, K_REGION, K_FREEARR_OFF, K_FREEARR_MAX. change (2^32) with 4294967296.
replace (shad (al_space_beg L + c * 4294967296 + 3758096384)) with (shad (al_space_beg L) + (c * 536870912 + 469762048))
by (unfold shad; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - A8; Z.div_mod_to_equations; lia).
replace (shad (al_space_beg L + c * 4294967296)) with (shad (al_space_beg L) + c * 536870912)
by (unfold shad; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - A8; Z.div_mod_to_equations; lia).
rewrite !shlen_eq. change (3758096384 / 8) with 469762048. change (536870912 / 8) with 67108864.
split; split.
- intros i Hi. replace (shad (al_space_beg L) + c * 536870912 + i) with (shad (al_space_beg L) + (c * 536870912 + i)) by lia. apply Z0'. lia.
- eapply wr_at_sub; [exact W0| unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia| lia| lia].
- intros i Hi. replace (shad (al_space_beg L) + (c * 536870912 + 469762048) + i) with (shad (al_space_beg L) + (c * 536870912 + 469762048 + i)) by lia. apply Z0'. lia.
- eapply wr_at_sub; [exact W0| unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia| lia| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End D.
End CANSEC1.
