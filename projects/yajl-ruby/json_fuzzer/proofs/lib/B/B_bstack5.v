(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Step Frame Arr NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow CompatE2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanRepFrame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_base B_alloc_iface B_iface B_live B_policy5 B_budget5 B_slack5 BI_shadow BI_lowshadow BI_gtrans BYajlRep BYajl_iface BF_place BF_fakestack_rep BF_fakestack BF_fakestack1 BF_fakestack0 B_bundle B_benv5 B_bframe B_bframe2 B_bframe4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

Ltac lia ::= LiaA.liaA.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Lemma rw_cells_reshape : forall m A cs cs',
  cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> cells_wf cs' ->
  rw_cells bsegs m A cs -> rw_cells bsegs m A cs'.
Proof.
  intros m A cs cs' HB HS HW [[_ B] W]. split; [split; [exact HW| rewrite HB; exact B]| rewrite HS; exact W].
Qed.

Lemma ff_live_class_cons : forall (LF : list fblock) N c x,
  ff_live_class ((c,x)::LF) N = if (c =? N) then S (ff_live_class LF N) else ff_live_class LF N.
Proof.
  intros. unfold ff_live_class. cbn. destruct (c =? N); reflexivity.
Qed.
Lemma ff_live_class_In : forall (LF : list fblock) N g, In (N, g) LF -> (1 <= ff_live_class LF N)%nat.
Proof.
  induction LF as [|[c x] LF IH]; intros N g Hg; [destruct Hg|]. rewrite ff_live_class_cons.
  destruct Hg as [E|Hg]; [injection E as -> ->; rewrite Z.eqb_refl; lia|].
  pose proof (IH N g Hg). destruct (c =? N); lia.
Qed.
Lemma ff_live_class_uniq : forall LF N, (ff_live_class LF N < 2)%nat ->
  forall f f', In (N, f) LF -> In (N, f') LF -> f = f'.
Proof.
  induction LF as [|[c x] LF IH]; intros N H f f' Hf Hf'; [destruct Hf|].
  rewrite ff_live_class_cons in H.
  destruct (Z.eqb_spec c N) as [E|NE].
  - subst c. destruct Hf as [Ef|Hf]; [| pose proof (ff_live_class_In LF N f Hf); lia].
    destruct Hf' as [Ef'|Hf']; [| pose proof (ff_live_class_In LF N f' Hf'); lia]. congruence.
  - destruct Hf as [Ef|Hf]; [congruence|]. destruct Hf' as [Ef'|Hf']; [congruence|]. exact (IH N H f f' Hf Hf').
Qed.

Ltac zground :=
  repeat match goal with
    | |- context [?a ^ ?e] => let v := eval vm_compute in (a ^ e) in change (a ^ e) with v
    | |- context [Z.shiftl ?a ?b] => let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
    | H : context [?a ^ ?e] |- _ => let v := eval vm_compute in (a ^ e) in change (a ^ e) with v in H
    | H : context [Z.shiftl ?a ?b] |- _ => let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v in H
    end.

Section Bundle.
(* [comment removed for export] *)
Variable StdioRep : stdout_st -> mem -> Prop.
Variable RTMisc : aenv -> mem -> Prop.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
#[local] Notation AHKc := (AHK StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (aS E0 FSB0 HR0).
#[local] Notation aNc := (aN E0 FSB0 HR0).
#[local] Notation aEBc := (aEB EB0).
#[local] Notation usp sp := (bv_unsigned sp).
Variable PL0 : fs_plumb.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Variable rt_fp : Z -> Prop.
Hypothesis RTMisc_agree : forall m m', RTMisc E0 m -> (forall a, rt_fp a -> m' (wa a) = m (wa a)) -> RTMisc E0 m'.
Hypothesis rt_fp_where : forall a, rt_fp a -> (0x10000 <= a < 0x603000 /\ ~ cl_cells a /\ ~ stdio_w a /\ ~ in_cells img_mut a) \/ rt_high2 E0 PL0 a.
Hypothesis RT_fsenv : forall m, RTMisc E0 m -> FSEnv bsegs E0 FSB0 PL0 m.
Variable so_fp : Z -> Prop.
Hypothesis StdioRep_agree : forall so m m', StdioRep so m -> (forall a, so_fp a -> m' (wa a) = m (wa a)) -> StdioRep so m'.
Hypothesis so_fp_where : forall a, so_fp a -> 0x10000 <= a < 0x603000 /\ ~ cl_cells a /\ ~ in_cells img_mut a.

#[local] Notation live_block_geom := (B_bframe.live_block_geom E0 FSB0).
#[local] Notation live_block_fs_sep := (B_bframe.live_block_fs_sep E0 FSB0).
#[local] Notation lazy_disjoint_img := (B_bframe.lazy_disjoint_img E0 FSB0 ENV0).
#[local] Notation lazy_disjoint_stack := (B_bframe.lazy_disjoint_stack E0 FSB0).
#[local] Notation lazy_disjoint_fs := (B_bframe.lazy_disjoint_fs E0 FSB0).
#[local] Notation pages_budgeted_A0 := (B_bframe.pages_budgeted_A0 E0 FSB0 HR0).
#[local] Notation In_A0_S0 := (B_bframe.In_A0_S0 E0 FSB0 HR0).
#[local] Notation fframe_pos := (B_bframe.fframe_pos).
#[local] Notation acc_ok_fs := (B_bframe2.acc_ok_fs E0 FSB0).
#[local] Notation lazy_disjoint_resv_range := (B_bframe4.lazy_disjoint_resv_range E0 FSB0).
#[local] Notation AHK_fs_call := (B_bframe4.AHK_fs_call StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK rt_fp RTMisc_agree rt_fp_where so_fp StdioRep_agree so_fp_where).

(* [comment removed for export] *)
Lemma sm_policies : forall s LB LF m mo lo (sp : word),
  AHKc s LB LF m mo -> alloc_ceiling <= lo ->
  let P := acc_ok (m_vm_lazy mo) (aSc s) in
     (forall a k, lo <= a -> a + Z.of_nat k <= usp sp -> P (Z_to_bv 64 a, k))
  /\ (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k))
  /\ (forall a k, fp_ctx PL0 <= a -> a + Z.of_nat k <= fp_ctx PL0 + 160 -> P (Z_to_bv 64 a, k))
  /\ (forall a k, ae_thread E0 <= a -> a + Z.of_nat k <= ae_thread E0 + 64 -> P (Z_to_bv 64 a, k))
  /\ (forall a k, fp_dtls PL0 <= a -> a + Z.of_nat k <= fp_dtls PL0 + 4096 -> P (Z_to_bv 64 a, k))
  /\ (forall a k, FSB0 <= a -> a + Z.of_nat k <= FSB0 + kFsBytes -> P (Z_to_bv 64 a, k))
  /\ (forall a k, FS_SB + FSB0 / 8 <= a -> a + Z.of_nat k <= FS_SB + (FSB0 + kFsBytes) / 8 -> P (Z_to_bv 64 a, k)).
Proof.
  intros s LB LF m mo lo sp H LOC. cbv zeta. pose proof H as H0. ahk_open H. pose proof B_bframe.ceil_range as CR.
  pose proof Henv as Henv0. destruct Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & _).
  unfold app_mem in V3. rewrite kLowAppEnd_val, kHighMemBeg_val in V3. rewrite kFsBytes_val in *.
  pose proof (bvu64 sp) as SPB.
  destruct PL0OK as ((c0 & cl & CRR & CC1 & CC2) & (d0 & dl & DRR & DD1 & DD2) & TRR & _).
  pose proof (resv_range_num _ _ _ CRR ltac:(clear -CC1 CC2; lia)) as (CN1 & CN2 & CN3 & CN4).
  pose proof (resv_range_num _ _ _ DRR ltac:(clear -DD1 DD2; lia)) as (DN1 & DN2 & DN3 & DN4).
  pose proof (resv_range_num _ _ _ TRR ltac:(clear; lia)) as (TN1 & TN2 & TN3 & TN4).
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - (* [comment removed for export] *) intros a k Ha Hk. eapply (B_bframe.acc_ok_of_lazy_disjoint mo _ lo (2^64)); [| clear -LOC CR; lia| clear; lia| exact Ha| clear -Hk SPB; lia].
    apply (lazy_disjoint_stack s mo _ _ Hkern Hwf Henv0). exact LOC.
  - (* [comment removed for export] *) intros a k Ha Hk. eapply (B_bframe.acc_ok_of_lazy_disjoint mo _ 0 0x603000); [| clear; lia| clear; lia| clear -Ha; lia| exact Hk].
    apply (lazy_disjoint_img s mo _ _ Hkern Hwf Henv0). clear; lia.
  - (* [comment removed for export] *) intros a k Ha Hk. eapply (B_bframe.acc_ok_of_lazy_disjoint mo _ c0 (c0 + cl)); [| clear -CN1; lia| clear -CN2 CR; lia| clear -Ha CC1; lia| clear -Hk CC2; lia].
    exact (lazy_disjoint_resv_range s mo c0 cl Hkern Hwf Henv0 CRR ltac:(clear -CC1 CC2; lia)).
  - (* [comment removed for export] *) intros a k Ha Hk. eapply (B_bframe.acc_ok_of_lazy_disjoint mo _ (ae_thread E0) (ae_thread E0 + 4096)); [| clear -TN1; lia| clear -TN2 CR; lia| exact Ha| clear -Hk; lia].
    exact (lazy_disjoint_resv_range s mo _ _ Hkern Hwf Henv0 TRR ltac:(clear; lia)).
  - (* [comment removed for export] *) intros a k Ha Hk. eapply (B_bframe.acc_ok_of_lazy_disjoint mo _ d0 (d0 + dl)); [| clear -DN1; lia| clear -DN2 CR; lia| clear -Ha DD1; lia| clear -Hk DD2; lia].
    exact (lazy_disjoint_resv_range s mo d0 dl Hkern Hwf Henv0 DRR ltac:(clear -DD1 DD2; lia)).
  - (* [comment removed for export] *) intros a k Ha Hk. rewrite <- EFS in Ha, Hk. exact (acc_ok_fs s mo _ a k Hwf Hkern Henv0 Ha Hk).
  - (* [comment removed for export] *) intros a k Ha Hk. unfold FS_SB in Ha, Hk. destruct Hfs as (P1 & P2 & P3 & P4 & _). rewrite EFS in P1, P2, P3.
    rewrite kFsBytes_val in P3.
    right. eapply (pages_budgeted_acc_inS _ (pgdn (sh FSB0)) (pgup (sh (FSB0 + 11571200)))).
    + eapply (pages_budgeted_A0 s (pgdn (sh FSB0)) (pgup (sh (FSB0 + 11571200)))); [| apply pgdn_mod| | | clear; lia| clear; lia].
      * apply In_A0_S0. unfold S0_ivs5. rewrite kFsBytes_val. do 3 right. left. reflexivity.
      * unfold pgdn, sh. rewrite A_SB_val. clear -P2. Z.div_mod_to_equations; lia.
      * unfold pgup, pgdn, sh. rewrite A_SB_val. clear -P2 P3 CR. Z.div_mod_to_equations; lia.
    + clear -Ha Hk P2 P3 CR. Z.div_mod_to_equations; lia.
    + unfold pgdn, sh. rewrite A_SB_val. clear -Ha P2. Z.div_mod_to_equations; lia.
    + unfold pgup, pgdn, sh. rewrite A_SB_val. clear -Hk P2 P3 CR. Z.div_mod_to_equations; lia.
    + unfold pgup, pgdn, sh. rewrite A_SB_val. clear -P2 P3 CR. Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma munch_img_untouched : forall W m m',
  munch W m m' -> Forall (fun iv => 0x603000 <= fst iv) W -> forall a, 0 <= a < AY_IMG_HI -> m' (wa a) = m (wa a).
Proof.
  clear. intros W m m' MU FW a Ha. unfold AY_IMG_HI in Ha. apply MU. rewrite wa_unsigned by (clear -Ha; lia).
  eapply outside_of_Forall; [exact FW|]. intros iv Hiv R. cbn beta in Hiv. clear -Ha Hiv R. lia.
Qed.

(* [comment removed for export] *)
Lemma astack_malloc1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : aps) (LB : list ablock) (LF : list fblock)
         (lo : Z) (K : TSet),
  K [] -> AHKc s LB LF m mo -> (ff_live_class LF 1 < 2)%nat ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK -> bv_unsigned sp <= 2^47 -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m -> tp = Z_to_bv 64 (c_tp ACONSTS) -> frm0 fc ->
  forall RR : Z, RR <= aps_credit s ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32)
          (m' : mem) (mo' : Model) (s' : aps) (ff : Z) (junk : list byte),
     stk bsegs m' lo (bv_unsigned sp) -> ay_pres LB LF (bv_unsigned sp) [] m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> frm0 fc' -> aps_so s' = aps_so s ->
     0 < ff -> ff mod ff_bytes 1 = 0 -> amem ff (ff_bytes 1) -> ff + ff_bytes 1 <= alloc_ceiling ->
     (forall f, In f LF -> snd f + ff_bytes (fst f) <= ff \/ ff + ff_bytes 1 <= snd f) ->
     rw_cells bsegs m' ff [CB (Z.to_nat (ff_bytes 1 - 8)) junk; C8 (Z_to_bv 64 (aflagB E0 FSB0 1 ff))] ->
     rw_cells bsegs m' (oshw_lo ff) [CB (Z.to_nat (Z.shiftl 8 1)) (repeat (Z_to_bv 8 0) (Z.to_nat (Z.shiftl 8 1)))] ->
     (exists fl, rw_cells bsegs m' (aflagB E0 FSB0 1 ff) [C1 fl]) ->
     AHKc s' LB ((1, ff) :: LF) m' mo' -> ayR s mo s' mo' -> RR <= aps_credit s' ->
     m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo -> (forall a, 0 <= a < AY_IMG_HI -> m' (wa a) = m (wa a)) ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 ff) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                             F' (ret_pc ra) fc' None m' (seg_rom bsegs)) mo') K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 SM1) fc None m (seg_rom bsegs)) mo) K.
Proof.
  intros until K. intros HK H UNI ST LOC LO SPH AL MI Htp FC RR HRR CONT.
  pose proof H as H0. ahk_open H. pose proof B_bframe.ceil_range as CR.
  pose proof Henv as Henv0. destruct Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & _).
  unfold app_mem in V3. rewrite kLowAppEnd_val, kHighMemBeg_val in V3. rewrite kFsBytes_val in *.
  pose proof (RT_fsenv m ltac:(rewrite <- EE; exact Hrt)) as ENV.
  pose proof Hfs as FS. rewrite EE, EFS in FS.
  pose proof FS as (P1 & P2 & P3 & P4 & HH & _). unfold FS_SB in P4. rewrite kFsBytes_val in P3, P4.
  destruct (HH 1 ltac:(unfold kFsClasses; clear; lia)) as [h HINT]. replace (FSB0 + 8 * 1) with (FSB0 + 8) in HINT by (clear; lia).
  unfold AMALLOC_STACK in LO. pose proof (bvu64 sp) as SPB.
  destruct (sm_policies s LB LF m mo lo sp H0 LOC) as (PSTK & PIMG & PCTX & PTHR & PDT & PFS & PFSH).
  eapply (srzA_evt bsegs (aSc s) (aNc s) (aEBc s) (m_vm_lazy mo)).
  - eapply (stack_malloc1_walk (acc_ok (m_vm_lazy mo) (aSc s)) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo E0 FSB0 PL0 (aps_fs s) LF FS_SB h ST LOC ltac:(clear -LO; lia) SPH AL MI Htp ENV FS);
      [ exact Hicp | reflexivity | exact HINT | exact (ff_live_class_uniq LF 1 UNI)
      | exact PSTK | exact PIMG | exact PCTX | exact PTHR | exact PDT | exact PFS | exact PFSH ].
  - exact (proj1 Hkm).
  - exact Hli.
  - reflexivity.
  - (* [comment removed for export] *)
    intros ms' mo' HQ Hag HLI' Hh'.
    destruct HQ as (pos & HPOS & FRESH & t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & hv & j1 & j2 & -> & MU & WM & MI' & ST' & HI' & FL' & FR' & SH').
    pose proof (bv_unsigned_in_range 64 h) as UHR. unfold bv_modulus in UHR.
    assert (HP : 0 <= pos < 8192).
    { destruct HPOS as [-> | ->]; change 8191 with (Z.ones 13); rewrite Z.land_ones by (clear -UHR; lia); change 8192 with (2^13); apply Z.mod_pos_bound; clear; lia. }
    assert (KP : fs_pos_ok 1 pos) by (split; [clear -HP; lia| unfold fs_nframes, kFsLog, kFsMinFrameLog; cbn; clear -HP; lia]).
    set (ff := ff1 FSB0 pos) in *.
    assert (FFQ : ff = fs_frame_addr FSB0 1 pos) by (symmetry; apply ff1_eq).
    assert (FLQ : aflagB E0 FSB0 1 ff = fl1 FSB0 pos) by (rewrite FFQ, aflagB_frame by (clear -HP; lia); apply fl1_eq).
    (* [comment removed for export] *)
    assert (FSW : Forall (B_bframe4.fs_w FSB0) (sm1_W sp FSB0 pos)).
    { unfold sm1_W, B_bframe4.fs_w, sh1. unfold fl1, ff1. rewrite kFsBytes_val.
      repeat (constructor; [cbn [fst snd]; first [left; clear -LOC LO; lia | right; left; clear -HP; lia | right; right; clear -HP P1; Z.div_mod_to_equations; lia] |]).
      constructor. }
    assert (FS' : FSRep bsegs E0 FSB0 (aps_fs s) ((1, ff) :: LF) m').
    { rewrite FFQ. eapply (FSRep_alloc1 bsegs E0 FSB0 (aps_fs s) (aps_fs s) LF m m' sp pos hv _ _ j1 j2 FS KP FRESH); try eassumption.
      clear -LOC LO. lia. }
    pose proof (AHK_fs_call s LB LF _ (aps_fs s) m m' mo mo' _ H0 MU WM MI' FSW FS' Hag HLI') as AHK'.
    assert (SEQ : aps_set_fs (aps_fs s) s = s) by (destruct s; reflexivity). rewrite SEQ in AHK'.
    pose proof (magree_frame _ _ Hag) as (Ffds & Fvm & Flz & Ffs & _).
    eapply (CONT t0' t1 t2 a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 F fc m' mo' s ff (j1 ++ le8 sp ++ j2)).
    + exact ST'.
    + (* [comment removed for export] *)
      intros a Ha CL _. split; [| apply WM]. apply MU. rewrite wa_unsigned by (clear -Ha; lia).
      unfold sm1_W, outside, sh1. unfold fl1, ff1. cbn [fst snd].
      destruct CL as [CL|[(b & Hb & CL)|[(f & Hf & CL)|CL]]].
      * (* [comment removed for export] *) clear -CL LOC LO SPH P2 P3 P4 HP Ha CR. repeat split; try exact I; Z.div_mod_to_equations; lia.
      * (* [comment removed for export] *)
        pose proof (live_block_geom s mo b Hwf Hkern Henv0 (blocks_match_In _ _ _ Hbm Hb)) as ((G1 & G2 & G3) & _).
        pose proof (live_block_fs_sep s mo _ _ Hwf Hkern Henv0 (blocks_match_In _ _ _ Hbm Hb)) as FSS.
        unfold A_IMG_END in G1. unfold A_LOWAPP_END, A_HIGH_BEG in G3. rewrite EFS in FSS.
        clear -CL G1 G2 G3 FSS HP P2 P3 P4 LOC LO SPH Ha CR. repeat split; try exact I; Z.div_mod_to_equations; lia.
      * (* [comment removed for export] *)
        destruct f as [N f0]. cbn [fst snd] in CL.
        destruct (fframe_pos E0 FSB0 (aps_fs s) LF m N f0 FS Hf) as (pf & Q0 & Q1 & Q2 & Q3 & Q4 & CASES).
        assert (DIFF : N = 1 -> pf <> pos).
        { intros -> ->. apply (proj2 (lf_mem_In _ _ _)) in Hf.
          destruct CASES as [(X & _)|(_ & _ & Ef & _)]; [clear -X; lia|]. subst f0.
          rewrite ff1_eq in FRESH. unfold ff1 in FRESH. rewrite FRESH in Hf. discriminate. }
        unfold ff_bytes in CL. rewrite A_SB_val in CL.
        destruct CASES as [(-> & PP & -> & _)|(-> & PP & -> & _)];
          [| specialize (DIFF eq_refl)]; zground; cbn in CL;
          clear -CL PP HP DIFF P2 P3 P4 LOC LO SPH Ha Q0 Q1 CR;
          (repeat split; try exact I; Z.div_mod_to_equations; lia).
      * (* [comment removed for export] *) unfold ay_static in CL. clear -CL HP P2 P3 P4 LOC LO SPH Ha CR. repeat split; try exact I; Z.div_mod_to_equations; lia.
    + exact WM.
    + exact MI'.
    + exact FC.
    + reflexivity.
    + subst ff; unfold ff1. clear -HP P2. lia.
    + subst ff; unfold ff1. change (ff_bytes 1) with 128. clear -P1 HP. Z.div_mod_to_equations; lia.
    + subst ff; unfold ff1, amem. change (ff_bytes 1) with 128. clear -P2 P3 P4 HP CR. lia.
    + subst ff; unfold ff1. change (ff_bytes 1) with 128. clear -P3 HP. lia.
    + (* [comment removed for export] *)
      intros [Nf f0] Hf. cbn [fst snd].
      destruct (fframe_pos E0 FSB0 (aps_fs s) LF m Nf f0 FS Hf) as (pf & Q0 & Q1 & Q2 & Q3 & Q4 & CASES).
      assert (DIFF' : Nf = 1 -> pf <> pos).
      { intros -> ->. apply (proj2 (lf_mem_In _ _ _)) in Hf.
        destruct CASES as [(X & _)|(_ & _ & Ef & _)]; [clear -X; lia|]. subst f0.
        rewrite ff1_eq in FRESH. unfold ff1 in FRESH. rewrite FRESH in Hf. discriminate. }
      subst ff; unfold ff1, ff_bytes.
      destruct CASES as [(-> & PP & -> & _)|(-> & PP & -> & _)]; [| specialize (DIFF' eq_refl)]; zground; clear -PP HP DIFF' Q0; lia.
    + (* [comment removed for export] *)
      rewrite FLQ. eapply rw_cells_reshape; [| | | exact FR'].
      * cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
      * reflexivity.
      * cbn. destruct FR' as [[(W1 & _ & W3 & _) _] _]. cbn in W1, W3. rewrite !length_app. cbn [length].
        change (Z.to_nat (ff_bytes 1 - 8)) with 120%nat. split; [clear -W1 W3; lia| split; exact I].
    + (* [comment removed for export] *)
      replace (oshw_lo ff) with (sh1 FSB0 pos) by (subst ff; unfold oshw_lo, sh1; rewrite A_SB_val; reflexivity).
      eapply rw_cells_reshape; [| | | exact SH']; [reflexivity| reflexivity| cbn; repeat split; reflexivity].
    + exists (Z_to_bv 8 1). rewrite FLQ. exact FL'.
    + exact AHK'.
    + split; reflexivity.
    + exact HRR.
    + exact Ffs.
    + exact Ffds.
    + apply (munch_img_untouched _ _ _ MU). unfold sm1_W, sh1, fl1, ff1. repeat (constructor; [cbn [fst snd]; clear -LOC LO P2 HP CR; Z.div_mod_to_equations; lia|]). constructor.
Qed.

(* [comment removed for export] *)
Lemma astack_malloc0 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : aps) (LB : list ablock) (LF : list fblock)
         (lo : Z) (K : TSet),
  K [] -> AHKc s LB LF m mo -> (ff_live_class LF 0 < 2)%nat ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK -> bv_unsigned sp <= 2^47 -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m -> tp = Z_to_bv 64 (c_tp ACONSTS) -> frm0 fc ->
  forall RR : Z, RR <= aps_credit s ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32)
          (m' : mem) (mo' : Model) (s' : aps) (ff : Z) (junk : list byte),
     stk bsegs m' lo (bv_unsigned sp) -> ay_pres LB LF (bv_unsigned sp) [] m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> frm0 fc' -> aps_so s' = aps_so s ->
     0 < ff -> ff mod ff_bytes 0 = 0 -> amem ff (ff_bytes 0) -> ff + ff_bytes 0 <= alloc_ceiling ->
     (forall f, In f LF -> snd f + ff_bytes (fst f) <= ff \/ ff + ff_bytes 0 <= snd f) ->
     rw_cells bsegs m' ff [CB (Z.to_nat (ff_bytes 0 - 8)) junk; C8 (Z_to_bv 64 (aflagB E0 FSB0 0 ff))] ->
     rw_cells bsegs m' (oshw_lo ff) [CB (Z.to_nat (Z.shiftl 8 0)) (repeat (Z_to_bv 8 0) (Z.to_nat (Z.shiftl 8 0)))] ->
     (exists fl, rw_cells bsegs m' (aflagB E0 FSB0 0 ff) [C1 fl]) ->
     AHKc s' LB ((0, ff) :: LF) m' mo' -> ayR s mo s' mo' -> RR <= aps_credit s' ->
     m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo -> (forall a, 0 <= a < AY_IMG_HI -> m' (wa a) = m (wa a)) ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 ff) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                             F' (ret_pc ra) fc' None m' (seg_rom bsegs)) mo') K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 SM0) fc None m (seg_rom bsegs)) mo) K.
Proof.
  intros until K. intros HK H UNI ST LOC LO SPH AL MI Htp FC RR HRR CONT.
  pose proof H as H0. ahk_open H. pose proof B_bframe.ceil_range as CR.
  pose proof Henv as Henv0. destruct Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & _).
  unfold app_mem in V3. rewrite kLowAppEnd_val, kHighMemBeg_val in V3. rewrite kFsBytes_val in *.
  pose proof (RT_fsenv m ltac:(rewrite <- EE; exact Hrt)) as ENV.
  pose proof Hfs as FS. rewrite EE, EFS in FS.
  pose proof FS as (P1 & P2 & P3 & P4 & HH & _). unfold FS_SB in P4. rewrite kFsBytes_val in P3, P4.
  destruct (HH 0 ltac:(unfold kFsClasses; clear; lia)) as [h HINT]. replace (FSB0 + 8 * 0) with FSB0 in HINT by (clear; lia).
  unfold AMALLOC_STACK in LO. pose proof (bvu64 sp) as SPB.
  destruct (sm_policies s LB LF m mo lo sp H0 LOC) as (PSTK & PIMG & PCTX & PTHR & PDT & PFS & PFSH).
  eapply (srzA_evt bsegs (aSc s) (aNc s) (aEBc s) (m_vm_lazy mo)).
  - eapply (stack_malloc0_walk (acc_ok (m_vm_lazy mo) (aSc s)) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo E0 FSB0 PL0 (aps_fs s) LF FS_SB h ST LOC ltac:(clear -LO; lia) SPH AL MI Htp ENV FS);
      [ exact Hicp | reflexivity | exact HINT | exact (ff_live_class_uniq LF 0 UNI)
      | exact PSTK | exact PIMG | exact PCTX | exact PTHR | exact PDT | exact PFS | exact PFSH ].
  - exact (proj1 Hkm).
  - exact Hli.
  - reflexivity.
  - (* [comment removed for export] *)
    intros ms' mo' HQ Hag HLI' Hh'.
    destruct HQ as (pos & HPOS & FRESH & t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & hv & j1 & j2 & -> & MU & WM & MI' & ST' & HI' & FL' & FR' & SH').
    pose proof (bv_unsigned_in_range 64 h) as UHR. unfold bv_modulus in UHR.
    assert (HP : 0 <= pos < 16384).
    { destruct HPOS as [-> | ->]; change 16383 with (Z.ones 14); rewrite Z.land_ones by (clear -UHR; lia); change 16384 with (2^14); apply Z.mod_pos_bound; clear; lia. }
    assert (KP : fs_pos_ok 0 pos) by (split; [clear -HP; lia| unfold fs_nframes, kFsLog, kFsMinFrameLog; cbn; clear -HP; lia]).
    set (ff := ff0 FSB0 pos) in *.
    assert (FFQ : ff = fs_frame_addr FSB0 0 pos) by (symmetry; apply ff0_eq).
    assert (FLQ : aflagB E0 FSB0 0 ff = fl0 FSB0 pos) by (rewrite FFQ, aflagB_frame by (clear -HP; lia); apply fl0_eq).
    assert (FSW : Forall (B_bframe4.fs_w FSB0) (sm0_W sp FSB0 pos)).
    { unfold sm0_W, B_bframe4.fs_w, sh0. unfold fl0, ff0. rewrite kFsBytes_val.
      repeat (constructor; [cbn [fst snd]; first [left; clear -LOC LO; lia | right; left; clear -HP; lia | right; right; clear -HP P1; Z.div_mod_to_equations; lia] |]).
      constructor. }
    assert (FS' : FSRep bsegs E0 FSB0 (aps_fs s) ((0, ff) :: LF) m').
    { rewrite FFQ. eapply (FSRep_alloc0 bsegs E0 FSB0 (aps_fs s) (aps_fs s) LF m m' sp pos hv _ _ j1 j2 FS KP FRESH); try eassumption.
      clear -LOC LO. lia. }
    pose proof (AHK_fs_call s LB LF _ (aps_fs s) m m' mo mo' _ H0 MU WM MI' FSW FS' Hag HLI') as AHK'.
    assert (SEQ : aps_set_fs (aps_fs s) s = s) by (destruct s; reflexivity). rewrite SEQ in AHK'.
    pose proof (magree_frame _ _ Hag) as (Ffds & Fvm & Flz & Ffs & _).
    eapply (CONT t0' t1 t2 a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 F fc m' mo' s ff (j1 ++ le8 sp ++ j2)).
    + exact ST'.
    + (* [comment removed for export] *)
      intros a Ha CL _. split; [| apply WM]. apply MU. rewrite wa_unsigned by (clear -Ha; lia).
      unfold sm0_W, outside, sh0. unfold fl0, ff0. cbn [fst snd].
      destruct CL as [CL|[(b & Hb & CL)|[(f & Hf & CL)|CL]]].
      * clear -CL LOC LO SPH P2 P3 P4 HP Ha CR. repeat split; try exact I; Z.div_mod_to_equations; lia.
      * pose proof (live_block_geom s mo b Hwf Hkern Henv0 (blocks_match_In _ _ _ Hbm Hb)) as ((G1 & G2 & G3) & _).
        pose proof (live_block_fs_sep s mo _ _ Hwf Hkern Henv0 (blocks_match_In _ _ _ Hbm Hb)) as FSS.
        unfold A_IMG_END in G1. unfold A_LOWAPP_END, A_HIGH_BEG in G3. rewrite EFS in FSS.
        clear -CL G1 G2 G3 FSS HP P2 P3 P4 LOC LO SPH Ha CR. repeat split; try exact I; Z.div_mod_to_equations; lia.
      * destruct f as [N f0]. cbn [fst snd] in CL.
        destruct (fframe_pos E0 FSB0 (aps_fs s) LF m N f0 FS Hf) as (pf & Q0 & Q1 & Q2 & Q3 & Q4 & CASES).
        assert (DIFF : N = 0 -> pf <> pos).
        { intros -> ->. apply (proj2 (lf_mem_In _ _ _)) in Hf.
          destruct CASES as [(_ & _ & Ef & _)|(X & _)]; [| clear -X; lia]. subst f0.
          rewrite ff0_eq in FRESH. unfold ff0 in FRESH. rewrite FRESH in Hf. discriminate. }
        unfold ff_bytes in CL. rewrite A_SB_val in CL.
        destruct CASES as [(-> & PP & -> & _)|(-> & PP & -> & _)];
          [specialize (DIFF eq_refl)|]; zground; cbn in CL;
          clear -CL PP HP DIFF P2 P3 P4 LOC LO SPH Ha Q0 Q1 CR;
          (repeat split; try exact I; Z.div_mod_to_equations; lia).
      * unfold ay_static in CL. clear -CL HP P2 P3 P4 LOC LO SPH Ha CR. repeat split; try exact I; Z.div_mod_to_equations; lia.
    + exact WM.
    + exact MI'.
    + exact FC.
    + reflexivity.
    + subst ff; unfold ff0. clear -HP P2. lia.
    + subst ff; unfold ff0. change (ff_bytes 0) with 64. clear -P1 HP. Z.div_mod_to_equations; lia.
    + subst ff; unfold ff0, amem. change (ff_bytes 0) with 64. clear -P2 P3 P4 HP CR. lia.
    + subst ff; unfold ff0. change (ff_bytes 0) with 64. clear -P3 HP. lia.
    + intros [Nf f0] Hf. cbn [fst snd].
      destruct (fframe_pos E0 FSB0 (aps_fs s) LF m Nf f0 FS Hf) as (pf & Q0 & Q1 & Q2 & Q3 & Q4 & CASES).
      assert (DIFF' : Nf = 0 -> pf <> pos).
      { intros -> ->. apply (proj2 (lf_mem_In _ _ _)) in Hf.
        destruct CASES as [(_ & _ & Ef & _)|(X & _)]; [| clear -X; lia]. subst f0.
        rewrite ff0_eq in FRESH. unfold ff0 in FRESH. rewrite FRESH in Hf. discriminate. }
      subst ff; unfold ff0, ff_bytes.
      destruct CASES as [(-> & PP & -> & _)|(-> & PP & -> & _)]; [specialize (DIFF' eq_refl)|]; zground; clear -PP HP DIFF' Q0; lia.
    + rewrite FLQ. eapply rw_cells_reshape; [| | | exact FR'].
      * cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
      * reflexivity.
      * cbn. destruct FR' as [[(W1 & _ & W3 & _) _] _]. cbn in W1, W3. rewrite !length_app. cbn [length].
        change (Z.to_nat (ff_bytes 0 - 8)) with 56%nat. split; [clear -W1 W3; lia| split; exact I].
    + replace (oshw_lo ff) with (sh0 FSB0 pos) by (subst ff; unfold oshw_lo, sh0; rewrite A_SB_val; reflexivity).
      eapply rw_cells_reshape; [| | | exact SH']; [reflexivity| reflexivity| cbn; repeat split; reflexivity].
    + exists (Z_to_bv 8 1). rewrite FLQ. exact FL'.
    + exact AHK'.
    + split; reflexivity.
    + exact HRR.
    + exact Ffs.
    + exact Ffds.
    + apply (munch_img_untouched _ _ _ MU). unfold sm0_W, sh0, fl0, ff0. repeat (constructor; [cbn [fst snd]; clear -LOC LO P2 HP CR; Z.div_mod_to_equations; lia|]). constructor.
Qed.

End Bundle.
End RC__1.
