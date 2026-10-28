From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA A_oid A_pk_defs A_pk_type A_pk_ecc_set_group.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_ecp_group_free P_ecp_keypair_init P_ecp_group_load P_pk_ecparams_A P_pk_wrap_eckey.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_checks.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition A_PK_USE_ECPARAMS_RFC8410 : Z := 0xb0ad4.

Definition pk_use_ecparams_rfc8410_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent)
    (ca : Z -> curve_addrs) (ONE : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs R HIA) (LB LF : list blk) (PKA info C : Z) (k : ecp_kp) (id lo : Z) (tag len : word)
    (m : mem) (mo : Model) : config -> Prop := fun c =>
  ((bv_unsigned tag mod 2^32 <> 0 \/ bv_unsigned len <> 0) /\
    exists (t0' t1' t2' a0 a1 a2 a3 a4 a5 a6 a7 t3' t4' t5' t6' : word) (m' : mem) (mo' : Model),
      c = mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                      t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom segs)) mo'
      /\ HK segs R HIA h mo'
      /\ mo_frame mo mo'
      /\ a0 = Z_to_bv 64 MBEDTLS_ERR_PK_KEY_INVALID_FORMAT
      /\ munch [(lo, bv_unsigned sp)] m m'
      /\ wmono segs m m'
      /\ mem_inv segs m'
      /\ stk segs m' lo (bv_unsigned sp)
      /\ HM segs R HIA h LB LF m')
  \/ (bv_unsigned tag mod 2^32 = 0 /\ bv_unsigned len = 0 /\
      pk_ecc_set_group_postA segs R HIA MT ca ONE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF
        PKA info C k id lo m mo c).

Definition pk_use_ecparams_rfc8410_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent)
    (ca : Z -> curve_addrs) (ONE : Z) (ECIS : list Z) (ENTRY : Z) : Prop :=
  forall (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (PKA info C id lo : Z)
    (idpad pP pA pB pX pY pZ pN hpad pd qX qY qZ : word) (PRM : Z) (tag pad len pv : word),
  let k := kp_init C idpad pP pA pB pX pY pZ pN hpad pd qX qY qZ in
  HM segs R HIA h LB LF m ->
  HK segs R HIA h mo ->
  (length LF < 512)%nat ->
  rw_cells segs m PKA [C8 (Z_to_bv 64 info); C8 (Z_to_bv 64 C)] ->
  PKA mod 8 = 0 ->
  0 < PKA ->
  In info ECIS ->
  aobj segs (arl_AL R) (hcs segs R HIA h) m PKA 16 ->
  client_range (arl_L R) (LB ++ fdata LF) lo PKA 16 ->
  PKA + 16 <= lo \/ bv_unsigned sp <= PKA ->
  PKA + 16 <= C \/ C + ECP_KEYPAIR_SIZE <= PKA ->
  ecp_keypair_at segs MT m LB C k ->
  In (C, ECP_KEYPAIR_SIZE) LB ->
  0 <= id < 2^31 ->
  stk segs m lo (bv_unsigned sp) ->
  arl_stklo R <= lo ->
  lo <= bv_unsigned sp - PK_ECC_SET_GROUP_STACK_A - arl_need_ecp R ->
  bv_unsigned sp <= htop segs R HIA h ->
  bv_unsigned sp mod 16 = 0 ->
  tp = Z_to_bv 64 (arl_tp R) ->
  mem_inv segs m ->
  bv_unsigned ra mod 2 = 0 ->
  havol segs R HIA h + pk_set_group_PHI <= AVOL_MAX ->
  hfr segs R HIA h + pk_set_group_FR <= FR_MAX ->
  cnt24 LB + C24_ECP_GROUP_LOAD <= C24MAX ->
  ro_cells segs m PRM [C4 tag; C4 pad; C8 len; C8 pv] ->
  aobj segs (arl_AL R) (hcs segs R HIA h) m PRM 24 ->
  PRM mod 8 = 0 ->
  0 < PRM ->
  PRM + 24 <= lo \/ bv_unsigned sp <= PRM ->
  a0 = Z_to_bv 64 PRM ->
  a1 = Z_to_bv 64 id ->
  a2 = Z_to_bv 64 PKA ->
  aevtS segs (pk_use_ecparams_rfc8410_postA segs R HIA MT ca ONE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                h LB LF PKA info C k id lo tag len m mo)
    (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
                (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)) mo).

Lemma rfc_zs0 : forall x, 0 <= zswrap 32 (zlow 32 x) -> 0 <= - zswrap 32 (zlow 32 x) -> x mod 2^32 = 0.
Proof.
  intros x H1 H2. unfold zswrap, zlow in *.
  replace (2 ^ (32 - 1)) with 2147483648 in * by reflexivity.
  replace (2 ^ 32) with 4294967296 in * by reflexivity.
  pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)).
  Z.div_mod_to_equations. lia.
Qed.

Section WalkRFC.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NEEDR : 0 <= arl_need_rt R.

  Section Run.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PKA id lo PRM : Z) (tag pad len pv : word).
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - PK_ECC_SET_GROUP_STACK_A - arl_need_ecp R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis IDB : 0 <= id < 2^31.
  Hypothesis PRA : PRM mod 8 = 0.
  Hypothesis PR0 : 0 < PRM.
  Hypothesis DPS : PRM + 24 <= lo \/ bv_unsigned sp <= PRM.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (arl_need_ecp_rt R) as NER; pose proof (arl_need_ecp_smalloc R) as NES;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Definition RP : machine_state -> Prop := fun ms =>
    exists m1 : mem,
      munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo (bv_unsigned sp) /\ HM asegs R HIA h LB LF m1
      /\ presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m1
      /\ (((bv_unsigned tag mod 2^32 <> 0 \/ bv_unsigned len <> 0)
           /\ exists (t0' t1' t2' a1 a2 a3 a4 a5 a6 a7 t3' t4' t5' t6' : word),
                ms = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 MBEDTLS_ERR_PK_KEY_INVALID_FORMAT) a1 a2 a3 a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m1 (seg_rom asegs))
          \/ (bv_unsigned tag mod 2^32 = 0 /\ bv_unsigned len = 0
           /\ exists (t0' t1' t2' a2 a3 a4 a5 a6 a7 t3' t4' t5' t6' : word),
                ms = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 PKA) (Z_to_bv 64 id) a2 a3 a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 A_PK_ECC_SET_GROUP) fc None m1
                         (seg_rom asegs))).

  Lemma rfc_walk : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    HM asegs R HIA h LB LF m -> stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    ro_cells asegs m PRM [C4 tag; C4 pad; C8 len; C8 pv] ->
    aobj asegs AL CS m PRM 24 ->
    evtA asegs AL CS RP
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PRM) (Z_to_bv 64 id) (Z_to_bv 64 PKA) a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_PK_USE_ECPARAMS_RFC8410) fc None m (seg_rom asegs)).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HH ST MI PAR OPAR.
    unfold A_PK_USE_ECPARAMS_RFC8410.
    rt_facts.
    pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| lia| lia]).
    pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
    pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(lia)) as PRES.
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    lxr_pose.
    lx_pre. lx_run_tac (PLAN [A_PK_ECC_SET_GROUP; 0xb0b48] [] 100%N). lx_tree.
    all: apply evtA_done; unfold RP.
    all: lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
    all: split; [assumption|].
    all: split; [assumption|].
    all: lxr_leaf.
    all: try (lazymatch goal with Hs : stk _ ?mx lo (bv_unsigned sp + -8), Hc : rw_cells _ ?mx (bv_unsigned sp + -8) [C8 ra] |- _ =>
           chunk_to_stk Hc; stk_merge_into Hs Hc; replace (bv_unsigned sp + -8 + 8) with (bv_unsigned sp) in Hs by lia end).
    all: split; [assumption|].
    all: split; [assumption|].
    all: split; [assumption|].
    all: split; [assumption|].
    - left. split.
      + left. intro E. lazymatch goal with Hz : zswrap 32 (zlow 32 (bv_unsigned tag)) + 1 <= 0 \/ _ |- _ =>
          unfold zswrap, zlow in Hz; rewrite E in Hz; cbn in Hz; lia end.
      + do 14 eexists. reflexivity.
    - right. split; [eapply rfc_zs0; eassumption|]. split; [lia|].
      do 13 eexists. reflexivity.
    - left. split.
      + right. lia.
      + do 14 eexists. reflexivity.
  Qed.
  End Run.

  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_SG.
  Hypothesis SM1 : arl_smalloc R 1 = A_SMALLOC_1_SG.
  Hypothesis RTCL : forall m, arl_rtc R m -> asan_rtc m.
  Variable MT : list modp_ent.
  Variable ca : Z -> curve_addrs.
  Variable ONE : Z.
  Hypothesis HGL : ecp_group_load_stmtA asegs R HIA MT ca ONE A_ECP_GROUP_LOAD_SG.

  Theorem A_pk_use_ecparams_rfc8410_spec_s :
    pk_use_ecparams_rfc8410_stmtA asegs R HIA MT ca ONE A_EC_INFOS A_PK_USE_ECPARAMS_RFC8410.
  Proof.
    pose proof (A_pk_ecc_set_group_spec R HIA MT ca ONE IMG UARG SM1 NS1 NEEDR RTCL HGL) as SG.
    unfold pk_use_ecparams_rfc8410_stmtA. intros until pv. cbv zeta.
    intros HH HK0 LFB HPKA ALP NZP EI OPKA CRP DSP DPC KP INC IDB ST LOS SLO TOP SPA TPV MI RA BUD BUDF C24H
           PAR OPAR PRA PR0 DPS -> -> ->.
    pose proof (hcs_ok asegs R HIA h) as CSOK.
    pose proof (hcs_stack asegs R HIA h) as SCS0.
    pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
    pose proof (arl_need_ecp_rt R) as NER.
    pose proof (art_lo asegs R HIA) as ALO.
    pose proof (hm_blocks_low asegs R HIA h LB LF m HH) as BLW.
    pose proof (BLW C ECP_KEYPAIR_SIZE ltac:(apply in_app_iff; left; exact INC)) as CLW.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| lia| lia]).
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ _ (conj HK0 (mo_frame_refl mo))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo).
    { eapply rfc_walk; eassumption. }
    intros ms1 P1. unfold RP in P1.
    destruct P1 as (m1 & MU & WM & MI1 & ST1 & HH1 & PW1 & P1).
    destruct P1 as [(NZ & t0' & t1' & t2' & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3' & t4' & t5' & t6' & ->)
                   |(Z1 & Z2 & t0' & t1' & t2' & b2 & b3 & b4 & b5 & b6 & b7 & t3' & t4' & t5' & t6' & ->)].
    - apply aevtA_done. intros mo1 [HK1 MF1].
      left. split; [exact NZ|].
      exists t0', t1', t2', (Z_to_bv 64 MBEDTLS_ERR_PK_KEY_INVALID_FORMAT), b1, b2, b3, b4, b5, b6, b7, t3', t4', t5', t6', m1, mo1.
      split; [reflexivity|]. split; [exact HK1|]. split; [exact MF1|]. split; [reflexivity|].
      split; [eapply munch_weaken; [|exact MU]; intros x Hx; cbn in Hx |- *; lia|].
      split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|]. exact HH1.
    - pose proof (presW_presA asegs R HIA h LB LF _ _ _ m m1 PW1) as HP01.
      assert (HPKA1 : rw_cells asegs m1 PKA [C8 (Z_to_bv 64 info); C8 (Z_to_bv 64 C)]).
      { eapply rw_cells_transport; [exact HPKA| exact MU| exact WM| cbn; lia]. }
      assert (OPKA1 : aobj asegs (arl_AL R) (hcs asegs R HIA h) m1 PKA 16).
      { eapply aobj_munch.
        all: try (lazymatch goal with |- munch _ _ _ => exact MU end).
        all: first [ exact CSOK | exact OPKA
                   | (constructor; [| constructor]; cbn [fst snd]; eapply crange_sub; [exact SCS| lia| lia]) ]. }
      assert (KP1 : ecp_keypair_at asegs MT m1 LB C (kp_init C idpad pP pA pB pX pY pZ pN hpad pd qX qY qZ)).
      { eapply ecp_keypair_at_munch; [exact KP| exact MU| exact WM| exact MI| exact MI1| cbn; unfold ECP_KEYPAIR_SIZE in *; lia|].
        intros d Hd HO. exfalso. clear - Hd HO. unfold kp_mpds, kp_init, grp_mpds, grp_init, pt_mpds, pt_init in Hd. cbn in Hd.
        repeat (destruct Hd as [<-|Hd]; [cbn in HO; discriminate|]). destruct Hd. }
      eapply aevtA_call.
      { intros mo1 [HK1 MF1].
        eapply SG with (h := h) (LB := LB) (LF := LF) (PKA := PKA) (info := info) (C := C) (id := id) (lo := lo)
                       (idpad := idpad) (pP := pP) (pA := pA) (pB := pB) (pX := pX) (pY := pY) (pZ := pZ) (pN := pN)
                       (hpad := hpad) (pd := pd) (qX := qX) (qY := qY) (qZ := qZ);
          first [ exact HH1 | exact HK1 | exact LFB | exact HPKA1 | exact ALP | exact NZP | exact EI | exact OPKA1 | exact CRP
                | exact DSP | exact DPC | exact KP1 | exact INC | exact IDB | exact ST1 | exact LOS | exact SLO | exact TOP
                | exact SPA | exact TPV | exact MI1 | exact RA | exact BUD | exact BUDF | exact C24H | reflexivity
                | match goal with |- ?g => idtac "SG-PRE-LEFT:" g end ]. }
      cbv beta. intros ms4 mo4 (mo1 & [HK1 MF1] & PO).
      apply aevtS_now. right. split; [exact Z1|]. split; [exact Z2|].
      unfold pk_ecc_set_group_postA in PO |- *.
      destruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m2 & mo2 & h2 & r & g' & NB & LB2
                      & E4 & MI2 & ST2 & MF2 & HP2 & REST).
      exists q0, q1, q2, qa1, qa2, qa3, qa4, qa5, qa6, qa7, q3, q4, q5, q6, m2, mo2, h2, r, g', NB, LB2.
      split; [exact E4|]. split; [exact MI2|]. split; [exact ST2|].
      split; [exact (mo_frame_trans _ _ _ MF1 MF2)|].
      split; [|exact REST].
      eapply presA_trans; [| exact HP2].
      eapply presA_weaken; [exact HP01| | | | | | ]; first [ intros b Hb; exact Hb | lia | intros x _; exact I ].
  Qed.
End WalkRFC.

Theorem A_pk_use_ecparams_rfc8410_spec : forall (R : art_layout) (HIA : artA asegs R) (MT : list modp_ent)
    (ca : Z -> curve_addrs) (ONE : Z),
  asan_img_ok (arl_AL R) ->
  arl_uar_got R = A_UAR_GOT_SG ->
  arl_smalloc R 1 = A_SMALLOC_1_SG ->
  0 <= arl_need_smalloc R ->
  0 <= arl_need_rt R ->
  (forall m, arl_rtc R m -> asan_rtc m) ->
  ecp_group_load_stmtA asegs R HIA MT ca ONE A_ECP_GROUP_LOAD_SG ->
  pk_use_ecparams_rfc8410_stmtA asegs R HIA MT ca ONE A_EC_INFOS A_PK_USE_ECPARAMS_RFC8410.
Proof. intros. eapply A_pk_use_ecparams_rfc8410_spec_s; eassumption. Qed.
