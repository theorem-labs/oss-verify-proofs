From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Cells Step Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub P_mpi_copy P_mpi_mul_stmt P_mpi_lset.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_opnd A_mpi_journey A_mpi_journey2
     A_mpi_zeroize_and_free A_mpi_copy A_mpi_core_mul A_mpi_add_abs_W A_mpi_mul_mpi_W A_mpi_lset.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxAMpiTac LxAEcpSums.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_checks.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc.
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia.

Definition A_MPI_MUL_MID : Z := 0x09ef28.
Definition A_MPI_MUL_KCL : Z := 0x09f1d4.

Definition mm_frb (c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 : word) : list cell :=
  [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 c64; C8 c72].

Tactic Notation "mb_apply" uconstr(Lm) :=
  first [ (eapply Lm; first [lx_is_mem_goal; eassumption | lazymatch goal with |- @eq (bv _) _ _ => reflexivity end | idtac])
        | (eapply aevtA_eq; [ apply lx_MS_regs | eapply Lm; first [lx_is_mem_goal; eassumption | lazymatch goal with |- @eq (bv _) _ _ => reflexivity end | idtac] ]) ];
  try lx_regs_eq; try lx_app.

Section WMB.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis CMUL : mpi_core_mul_stmtA asegs R HIA A_MPI_CORE_MUL.
  Hypothesis LSET : mpi_lset_stmtA asegs R HIA A_MPI_LSET.
  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_MM.
  Hypothesis AMC : arl_amemcpy R = A_ASAN_MEMCPY_MM.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Variables (gp tp spv spe xs2 xs8 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own) (dA dB : mpd) (lo d1 : Z).
  Variable POST : config -> Prop.
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Local Notation SZB := (mul_mid_SZ nX dA dB).
  Hypothesis JC : forall c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 : word,
    JCA asegs R HIA h LB LF m dX spv lo 80 (mm_frb c0 c8 c16 c24 c32 c40 c48 c56 c64 c72).
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis D0 : 0 <= d1.
  Hypothesis NRA : 0 <= md_n dA <= 10000.
  Hypothesis NRB : 0 <= md_n dB <= 10000.
  Hypothesis NXA : md_addr dA <> X.
  Hypothesis NXB : md_addr dB <> X.
  Hypothesis SPE : bv_unsigned spv + 16 <= bv_unsigned spe.
  Hypothesis BUD : havol asegs R HIA h + mul_mid_PHI dA dB <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + mul_mid_FR d1 + fr_charge 0 <= FR_MAX.
  Hypothesis SLO2 : lo <= bv_unsigned spv - 80 - 240 - arl_need_rt R.
  Hypothesis C24H : cnt24 LB + 2 <= C24MAX.
  Hypothesis XSL : rw_cells asegs m (bv_unsigned spv + 40) [C8 (Z_to_bv 64 X)].
  Hypothesis XSD : X + 16 <= bv_unsigned spv + 40 \/ bv_unsigned spv + 48 <= X.
  Hypothesis XSC : bv_unsigned spv + 48 <= hstkhi asegs R HIA h.
  Hypothesis XUW : uw_obj R X 16 d1.

  Definition KCLB_stmt : Prop :=
    forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (r : Z)
           (c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 : word)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 : word),
      XJA asegs R HIA h LB LF m dX spv lo 80 (mm_frb c0 c8 c16 c24 c32 c40 c48 c56 c64 c72) [] v f hc LBc mc dXc ->
      (r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) ->
      v <= mul_mid_PHI dA dB -> f <= mul_mid_FR d1 + fr_charge 0 -> md_n dXc <= SZB ->
      aevtA asegs (KF asegs R HIA hc mo) POST
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned spv + -80)) gp tp xt0 xt1 xt2 spe (Z_to_bv 64 (bv_unsigned spv + -80))
                 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 r) xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 A_MPI_MUL_KCL) fc None mc (seg_rom asegs)).
  Hypothesis KCL : KCLB_stmt.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L18349620061.2000007S2dE2EB".
  Lemma mb_view : forall (dE : mpd) (v f : Z) (fr : list cell) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd),
      XJA asegs R HIA h LB LF m dX spv lo 80 fr [] v f hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dE hc LBc mc dXc ->
      md_addr dE <> X ->
      rw_cells asegs mc (md_addr dE) [C8 (Z_to_bv 64 (md_p dE)); C2 (Z_to_bv 64 (md_sg dE)); C2 (Z_to_bv 64 (md_n dE)); C4 (md_pad dE)] /\
      aobj asegs AL (hcs asegs R HIA hc) mc (md_addr dE) 16 /\
      (md_sg dE = 1 \/ md_sg dE = -1) /\ 0 < md_addr dE /\ md_addr dE + 16 <= 2 ^ 64 /\ md_addr dE mod 8 = 0.
  Proof.
    intros dE v f fr hc LBc mc dXc J [E|[DBJ B]] NE; [exfalso; exact (NE E)|].
    pose proof (opnd_viewA _ _ _ _ _ _ _ (bj_at _ _ _ _ _ _ _ _ _ _ B)) as [(CE & EAL & E0 & _) SGE]. unfold mpi_cells in CE.
    pose proof (rw_cells_bound _ _ _ _ CE) as EB. cbn [cells_size csize Nat.add] in EB.
    split; [exact CE|]. split; [exact (bj_aobj _ _ _ _ _ _ _ _ _ _ B)|]. split; [exact SGE|]. split; [exact E0|]. split; [clear - EB; lia| exact EAL].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L11762681116.2L20422897925.4L20422899211.2L59308666361.300000800E00L00VS2dE3EN1S1R2dE3ACV2HCS2dE2HIS2dE2N12EZ".
  Lemma mb_scanf : forall (dE : mpd) (v f : Z) (fr : list cell) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd),
      XJA asegs R HIA h LB LF m dX spv lo 80 fr [] v f hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dE hc LBc mc dXc ->
      md_addr dE <> X -> 1 <= md_n dE ->
      bytes_at asegs mc (md_p dE) (u32s (md_limbs dE)) /\ Z.of_nat (length (md_limbs dE)) = md_n dE /\ 0 < md_p dE /\
      aobj asegs AL (hcs asegs R HIA hc) mc (md_p dE) (4 * md_n dE) /\ md_p dE mod 4 = 0 /\ md_p dE + 4 * md_n dE < 2 ^ 64.
  Proof.
    intros dE v f fr hc LBc mc dXc J [E|[DBJ B]] NE N1; [exfalso; exact (NE E)|].
    pose proof (JC spv spv spv spv spv spv spv spv spv spv) as JCc.
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    destruct (limb_own_eq_dec (md_own dE) LNull) as [EN|EN].
    - destruct (OWNE0 EN) as [_ EZ]. exfalso. clear - EZ N1. lia.
    - destruct (OWNE1 EN) as (EN1 & EP0 & EPAL & EBY & ESK & BHP & BST).
      split; [exact EBY|]. split; [exact LENE|]. split; [exact EP0|].
      split; [exact (bj_aobjL _ _ _ _ _ _ _ _ _ _ B EN)|]. split; [exact EPAL|].
      pose proof (alloc_ceiling_val R) as ACV.
      destruct (md_own dE) eqn:EOA; [exfalso; exact (EN eq_refl)| |].
      + destruct (BHP eq_refl) as [_ BINc].
        pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HH1. cbn [app] in HH1.
        destruct (hm_apart asegs R HIA hc LBc LF mc HH1) as [HBR _]. rewrite Forall_forall in HBR.
        destruct (HBR _ ltac:(apply in_app_iff; left; exact BINc)) as (_ & _ & HC & _). cbn [fst snd] in HC. clear - HC ACV. lia.
      + destruct (BST eq_refl) as [BRO|[_ BH]]; [| exact BH].
        destruct (A_mpi_copy.static_limbs_low (Z_to_bv 64 0) mc _ _ _ EBY LENE ltac:(clear - EN1; lia) BRO) as [_ HI]. clear - HI. lia.
  Qed.

  Local Ltac mb_base hc J :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF';
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV;
    pose proof (xa_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as MI1.

  Local Ltac mb_show :=
    match goal with
    | |- context [MS _ _ ?pc _ _ _ (seg_rom _)] => idtac "LEFT-PC:" pc
    | |- ?g => idtac "LEFT:" g
    end.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0090>L10568909570.7L11868152746.1L22961942245.0L2333536794.11L39280637297.0L48191417473.5L52419075592.0L59308587280.2L61786126333.500000I00N00O01601701I01J01P01cS3spv2lo3dXc4LOSP4LEN12XLS3spvSS1R3HIA1h3spv2lo5NEEDR3LOS3SLO3TOP1a2HaSS3spv2lo4LOSP1a2NOSS1q2HqS3spv1X2lo4LOSP3DSX".
  Lemma mb_frst : forall (EX : list blk) (v f : Z) (c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 : word)
           (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (m' : mem),
      XJA asegs R HIA h LB LF m dX spv lo 80 (mm_frb c0 c8 c16 c24 c32 c40 c48 c56 c64 c72) EX v f hc LBc mc dXc ->
      munch [(bv_unsigned spv + -80, bv_unsigned spv)] mc m' -> wmono asegs mc m' -> mem_inv asegs m' ->
      stk asegs m' lo (bv_unsigned spv + -80) ->
      rw_cells asegs m' (bv_unsigned spv + -80) (mm_frb k0 k8 k16 k24 k32 k40 k48 k56 k64 k72) ->
      XJA asegs R HIA h LB LF m dX spv lo 80 (mm_frb k0 k8 k16 k24 k32 k40 k48 k56 k64 k72) EX v f hc LBc m' dXc.
  Proof.
    intros until m'. intros J MU WM MI' ST' FR'.
    pose proof (JC c0 c8 c16 c24 c32 c40 c48 c56 c64 c72) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 80 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof (xa_XLS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as XLS1.
    pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HH1.
    pose proof (xa_top _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HT1.
    replace (bv_unsigned spv + -80) with (bv_unsigned spv - 80) in ST', FR', MU by (clear; lia).
    assert (HH' : HM asegs R HIA hc (EX ++ LBc) LF m').
    { eapply (hm_munch asegs R HIA hc (EX ++ LBc) LF _ mc m' HH1 MU WM).
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. left. left. rewrite HT1. clear - Ha LOS SLO TOP NEEDR. lia. }
    assert (ARR' : u32arr asegs m' (md_p dXc) (md_limbs dXc)).
    { destruct (limb_own_eq_dec (md_own dXc) LNull) as [EO|NEO].
      - ddestruct (OWN0 EO) as (EP & EN & EL). rewrite EP, EL. unfold u32arr, bytes_at, wr_at. cbn [u32s flat_map length Z.of_nat Z.mul].
        split; (split; [clear; lia| split; [clear; lia| intros q Hq; exfalso; clear - Hq; lia]]).
      - ddestruct (OWN1 NEO) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47).
        eapply (u32arr_transport asegs [(bv_unsigned spv - 80, bv_unsigned spv)] mc m'); [exact XARR| exact MU| exact WM|].
        cbn [disjoint_from]. split; [| exact I]. pose proof (XLS1 NEO) as XL. clear - XL LEN1 LOSP N1. lia. }
    pose proof (xa_limbs_fr asegs R HIA h LB LF m dX spv lo 80 _ (mm_frb k0 k8 k16 k24 k32 k40 k48 k56 k64 k72) JCc _ _ _ _ _ _ _ _ m' (md_limbs dXc) J MU WM MI' ST' HH'
                  ltac:(intros a NO; right; cbn [outside] in NO; clear - NO LOSP; lia) FR'
                  ltac:(cbn [disjoint_from md_addr]; split; [clear - DSX LOSP; lia| exact I]) ARR' eq_refl) as J'.
    destruct dXc. exact J'.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L20604680353.5L30118417173.8L46655178105.5L63880477479.500000C00Z00n01AS3spv2lo2dE4LOSP2ESS1R3HIA1h3spv3TOP5HTOP0S3spv2lo2dE4LOSP3EL5S1R3spv2lo3LOS4LOSP".
  Lemma mb_frride : forall (dE : mpd) (EX : list blk) (v f : Z) (c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 : word)
           (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (m' : mem),
      XJA asegs R HIA h LB LF m dX spv lo 80 (mm_frb c0 c8 c16 c24 c32 c40 c48 c56 c64 c72) EX v f hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dE hc LBc mc dXc ->
      munch [(bv_unsigned spv + -80, bv_unsigned spv)] mc m' -> wmono asegs mc m' ->
      rideA R HIA LB LF m dX spv lo dE hc LBc m' dXc.
  Proof.
    intros dE EX v f c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 hc LBc mc dXc m' J [E|[DBJ B]] MU WM; [left; exact E| right; split; [exact DBJ|]].
    pose proof (JC c0 c8 c16 c24 c32 c40 c48 c56 c64 c72) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 80 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    pose proof (xa_stkhi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HS1.
    pose proof (hcs_stack asegs R HIA hc) as SCS0. pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP0.
    eapply bja_munch; [exact J| exact B| exact MU| exact WM| | |].
    - unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS0| clear - LOS LOSP; lia| rewrite HS1; clear - HTOP0 TOP LOSP; lia]| apply Forall_nil].
    - cbn [disjoint_from]. split; [clear - ES LOSP; lia| exact I].
    - intros BN. cbn [disjoint_from]. split; [ddestruct (OWNE1 BN) as (_ & _ & _ & _ & EL5 & _); clear - EL5 LOSP; lia| exact I].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L1000762305.4 L52101693566.6L62037129548.600000A00S00kS3spv2lo3LO04LOSPS1R3HIA1h3spv1a2HaS1R3spv2lo4LOSP4SP643LOS".
  Lemma mb_fruwc : forall mc m',
      uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned spe) (bv_unsigned spv) d1 ->
      munch [(bv_unsigned spv + -80, bv_unsigned spv)] mc m' ->
      uwc asegs m' (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned spe) (bv_unsigned spv) d1.
  Proof.
    intros mc m' UW MU. pose proof (JC spv spv spv spv spv spv spv spv spv spv) as JCc.
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 80 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & _).
    pose proof (jca_LOS _ _ _ _ _ _ _ _ _ _ _ _ JCc) as LOS.
    eapply uwc_munch; [exact UW| exact MU| clear - LO0 LOSP; lia| apply hstkhi_le64; clear - LOS LOSP SP64; lia|].
    intros a Ha. cbn [outside]. split; [clear - Ha; lia| exact I].
  Qed.

  Lemma mb_frall : forall (v f : Z) (c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 : word)
           (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (W : list ivl) (m' : mem),
      XJA asegs R HIA h LB LF m dX spv lo 80 (mm_frb c0 c8 c16 c24 c32 c40 c48 c56 c64 c72) [] v f hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dA hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dB hc LBc mc dXc ->
      uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned spe) (bv_unsigned spv) d1 ->
      munch W mc m' -> sub_fp W [(bv_unsigned spv + -80, bv_unsigned spv)] ->
      wmono asegs mc m' -> mem_inv asegs m' ->
      stk asegs m' lo (bv_unsigned spv + -80) ->
      rw_cells asegs m' (bv_unsigned spv + -80) (mm_frb k0 k8 k16 k24 k32 k40 k48 k56 k64 k72) ->
      XJA asegs R HIA h LB LF m dX spv lo 80 (mm_frb k0 k8 k16 k24 k32 k40 k48 k56 k64 k72) [] v f hc LBc m' dXc /\
      rideA R HIA LB LF m dX spv lo dA hc LBc m' dXc /\
      rideA R HIA LB LF m dX spv lo dB hc LBc m' dXc /\
      uwc asegs m' (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned spe) (bv_unsigned spv) d1.
  Proof.
    intros until m'. intros J RA RB UW MU0 SUB WM MI ST FR.
    pose proof (munch_weaken _ _ _ _ SUB MU0) as MU.
    split; [exact (mb_frst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J MU WM MI ST FR)|].
    split; [eapply (mb_frride dA); [exact J| exact RA| exact MU| exact WM]|].
    split; [eapply (mb_frride dB); [exact J| exact RB| exact MU| exact WM]|].
    exact (mb_fruwc _ _ UW MU).
  Qed.

  Local Ltac mb_frame J :=
    let FR := fresh "FR" in let ST := fresh "ST" in
    pose proof (xa_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as FR;
    pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as ST;
    unfold mm_frb in FR;
    replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) in FR, ST by (clear; lia).

  Local Ltac mb_scs hc J LOS TOP HH :=
    let SCS := fresh "SCS" in let SCS0 := fresh "SCS0" in let HS1 := fresh "HS1" in let HTq := fresh "HTq" in
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (xa_stkhi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HS1;
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTq;
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned spv - lo))
      by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; clear - HTq TOP; lia]).

  Local Ltac mb_hyps mx :=
    repeat match goal with H : context [mx] |- _ => let T := type of H in idtac "HYP:" T; clear H end.

  Local Ltac mb_frleaf J RA RB UW :=
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] =>
      lazymatch goal with
      | MU : munch _ _ mx, WM : wmono _ _ mx, MI : mem_inv _ mx, ST : stk _ mx lo _, FR : rw_cells _ mx (bv_unsigned spv + -80) _ |- _ =>
          let J' := fresh "J" in let RA' := fresh "RA" in let RB' := fresh "RB" in let UW' := fresh "UW" in
          destruct (mb_frall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J RA RB UW MU
                       ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [outside] in Hx |- *; lia) WM MI ST FR)
            as (J' & RA' & RB' & UW')
      end end.

  Local Ltac mb_budget :=
    try (right; reflexivity);
    try (unfold lset_FR, mul_mid_PHI, mul_mid_FR, grow_PHI, calls_FR, fr_charge, AVOL_CALL in *; lia).

  Lemma mb_lset_keep : forall LBq dq vq r dq', lset_R vq dq LBq r dq' -> binop_keep LBq dq dq'.
  Proof.
    intros LBq dq vq r dq' [CR1 [CA CF]]. split; [exact CA|]. destruct CR1 as [(_ & EN & _ & _ & _ & EP)|(_ & ->)].
    - split; [exact EP|]. split; [exact CF|]. rewrite EN. apply Z.le_max_l.
    - split; [reflexivity|]. split; [exact CF| apply Z.le_refl].
  Qed.

  Lemma mb_ride_call : forall (dE : mpd) (c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 : word) (v f : Z)
           (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (m' : mem) (h' : HST asegs R HIA) (LB' : list blk) (dX' : mpd) (SPc : Z),
      XJA asegs R HIA h LB LF m dX spv lo 80 (mm_frb c0 c8 c16 c24 c32 c40 c48 c56 c64 c72) [] v f hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dE hc LBc mc dXc ->
      lo <= SPc <= bv_unsigned spv - 80 ->
      mem_inv asegs m' ->
      presA asegs R (mpd_keep LBc dXc) LF SPc (arl_stklo R) (hstkhi asegs R HIA hc) [(X, X + 16)] mc m' ->
      (forall x, hcs asegs R HIA hc x -> hcs asegs R HIA h' x) ->
      HM asegs R HIA h' LB' LF m' -> mpd_at asegs m' LB' dX' -> mpd_out LBc dXc LB' dX' ->
      (forall b, In b (mpd_blk dX') -> In b (mpd_blk dXc) \/ fresh_apart R (mpd_keep LBc dXc) LF (fst b) (snd b)) ->
      rideA R HIA LB LF m dX spv lo dE h' LB' m' dX'.
  Proof.
    intros dE c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 v f hc LBc mc dXc m' h' LB' dX' SPc J [E|[DBJ B]] HSP MI2 HP2 HCS2 HH2 MX2 OUT2 FRA2;
      [left; exact E| right; split; [exact DBJ|]].
    exact (bja_call asegs R HIA h LB LF m dX spv lo 80 _ (JC c0 c8 c16 c24 c32 c40 c48 c56 c64 c72) dE DBJ _ _ _ _ _ _ m' h' LB' dX' SPc J B HSP MI2 HP2 HCS2 HH2 MX2 OUT2 FRA2).
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0>L10510931130.3L11762681116.2L20422897925.4L20422899211.2L22961942245.0L25721262433.4L34389855963.2L39280637297.0L40362700714.0L53134459733.2L59031206751.1L59308585216.2L59308587280.2L59308666361.4L60451556164.300000900A00N00U00V00b00j00k00l01401801>01D01R01\S2dE1k2HKS2dE3EN1S1R2dE3ACV2HCS2dE2HISS2dE1k2HK2EZS3dXc2P0SSS2lo3LO0S2dES1a2HaS1q2HqS2dE1l4LENE2EZS2dE3dXc1K".
  Lemma mb_limbs : forall (dE : mpd) (v f : Z) (c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 : word)
           (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (k : Z),
      XJA asegs R HIA h LB LF m dX spv lo 80 (mm_frb c0 c8 c16 c24 c32 c40 c48 c56 c64 c72) [] v f hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dE hc LBc mc dXc ->
      md_addr dE <> X -> md_own dXc = LHeap -> 0 <= k <= md_n dE ->
      bytes_at asegs mc (md_p dE) (u32s (md_limbs dE)) /\ Z.of_nat (length (md_limbs dE)) = md_n dE /\
      (md_p dE + 4 * md_n dE <= md_p dXc \/ md_p dXc + 4 * md_n dXc <= md_p dE) /\
      md_p dE mod 4 = 0 /\ (k = 0 \/ 0 < md_p dE) /\ md_p dE + 4 * md_n dE < 2 ^ 64 /\
      (md_p dE + 4 * md_n dE <= lo \/ bv_unsigned spv <= md_p dE) /\
      aobj asegs AL (hcs asegs R HIA hc) mc (md_p dE) (4 * k).
  Proof.
    intros dE v f c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 hc LBc mc dXc k J [E|[DBJ B]] NE EO HK; [exfalso; exact (NE E)|].
    pose proof (JC c0 c8 c16 c24 c32 c40 c48 c56 c64 c72) as JCc.
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 80 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47).
    pose proof (alloc_ceiling_val R) as ACV.
    pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HH1. cbn [app] in HH1.
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    destruct (limb_own_eq_dec (md_own dE) LNull) as [EN|EN].
    - destruct (OWNE0 EN) as [EP EZ]. rewrite EP, EZ.
      assert (EL : md_limbs dE = []) by (destruct (md_limbs dE); [reflexivity| exfalso; cbn [length] in LENE; clear - LENE EZ; lia]).
      rewrite EL. assert (K0 : k = 0) by (clear - HK EZ; lia). subst k.
      split; [unfold bytes_at; cbn [u32s flat_map length Z.of_nat]; split; [clear; lia|]; split; [clear; lia|]; intros q Hq; exfalso; clear - Hq; lia|].
      split; [reflexivity|]. split; [left; clear - P0; lia|]. split; [reflexivity|]. split; [left; reflexivity|]. split; [clear; lia|].
      split; [left; clear - LO0; lia|].
      split; [intros a Ha; exfalso; clear - Ha; lia| intros a Ha; exfalso; clear - Ha; lia].
    - ddestruct (OWNE1 EN) as (EN1 & EP0 & EPAL & EBY & ESK & BHP & BST).
      split; [exact EBY|]. split; [exact LENE|].
      split; [pose proof (bj_sepL _ _ _ _ _ _ _ _ _ _ B EO EN) as K; clear - K; lia|].
      split; [exact EPAL|]. split; [right; exact EP0|].
      split.
      { destruct (md_own dE) eqn:EOA; [exfalso; exact (EN eq_refl)| |].
        - destruct (BHP eq_refl) as [_ BINc]. destruct (hm_apart asegs R HIA hc LBc LF mc HH1) as [HBR _]. rewrite Forall_forall in HBR.
          destruct (HBR _ ltac:(apply in_app_iff; left; exact BINc)) as (_ & _ & HC & _). cbn [fst snd] in HC. clear - HC ACV. lia.
        - destruct (BST eq_refl) as [BRO|[_ BH]]; [| exact BH].
          destruct (A_mpi_copy.static_limbs_low (Z_to_bv 64 0) mc _ _ _ EBY LENE ltac:(clear - EN1; lia) BRO) as [_ HI]. clear - HI. lia. }
      split; [exact ESK|].
      eapply aobj_sub; [exact (bj_aobjL _ _ _ _ _ _ _ _ _ _ B EN)| clear; lia| clear - HK; lia].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L1164172544.1   L22706556809.173L22706556809.174L35629214198.1  L35667858935.6  L35668120833.7  L41272598402.142L41272598402.143L44082271972.1  L44423159706.3  L51099750337.5  L60098763854.3  00000300j01a01f02:02R03D04604;04F04Y04cS1XS3spv1X3xs02dA2dB3dXc2c02c83c163c243c323c403c482fl1x2HxS3spv1X3xs02dA2dB3dXc2c02c83c163c243c323c403c482fl1x2HxS3spvS1R3HIA1h3spv2lo3XSCS1R3HIA1h3spv2lo3TOP3HTqS3spv1X3xs02dA2dB3dXc2c02c83c163c243c323c403c482flS3spv1X3xs02dA2dB3dXc2c02c83c163c243c323c403c482flS3spvS3spv1X3XSDS1R3spv2lo3LOS4LOSPS1R2lo3LOS".
  Lemma mb_SIGN : forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
           (c0 c8 c16 c24 c32 c40 c48 fl : word)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs6 xs7 xs10 xs11 xt3 xt4 xt5 xt6 : word),
      XJA asegs R HIA h LB LF m dX spv lo 80
        (mm_frb c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dB + 8)) fl (Z_to_bv 64 (md_addr dA + 8))) [] v f hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dA hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dB hc LBc mc dXc ->
      v <= mul_mid_PHI dA dB -> f <= mul_mid_FR d1 + fr_charge 0 -> md_n dXc <= SZB ->
      aevtA asegs (KF asegs R HIA hc mo) POST
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned spv + -80)) gp tp xt0 xt1 xt2 spe (Z_to_bv 64 (bv_unsigned spv + -80))
                 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                 xs2 (Z_to_bv 64 (al_sb AL)) xs4 xs5 xs6 xs7 xs8 fl xs10 xs11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x9f348) fc None mc (seg_rom asegs)).
  Proof.
    intros v f hc LBc mc dXc c0 c8 c16 c24 c32 c40 c48 fl xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs6 xs7 xs10 xs11 xt3 xt4 xt5 xt6 J RA RB BV BF SZ.
    pose proof (JC c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dB + 8)) fl (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 80 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    destruct (mb_view dA _ _ _ _ _ _ _ J RA NXA) as (CEA & OEA & SGA & A0 & A16 & AAL).
    destruct (mb_view dB _ _ _ _ _ _ _ J RB NXB) as (CEB & OEB & SGB & B0 & B16 & BAL).
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    unfold mpi_cells in CX1. cbn [md_addr md_pad] in CX1.
    pose proof (xa_aobjX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as OX1. cbn [md_addr] in OX1.
    pose proof (xa_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HPX1.
    assert (XSLc : rw_cells asegs mc (bv_unsigned spv + 40) [C8 (Z_to_bv 64 X)]).
    { eapply presA_rw_cells; [exact HPX1| exact XSL| apply client_range_stack; clear; lia|].
      replace (Z.of_nat (cells_size [C8 (Z_to_bv 64 X)])) with 8 by reflexivity. cbn [disjoint_from md_addr]. split; [| exact I].
      clear - XSD; lia. }
    clear HPX1.
    mb_base hc J. mb_frame J. mb_scs hc J LOS TOP HH.
    assert (SCS8 : crange (hcs asegs R HIA hc) lo (bv_unsigned spv + 48 - lo))
      by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; clear - XSC; lia]).
    lx_pre. lx_run_tac (PLAN [0x9f1d4; 0x9f3b0] [(0x9f368, DJoin); (0x9f384, DJoin); (0x9f3a0, DJoin)] 60%N). lx_tree.
    all: pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HHc; cbn [app] in HHc.
    all: pose proof (xa_top _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HT1.
    all: pose proof (xa_cwX _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J) as CWX; cbn [md_addr] in CWX; rewrite <- HT1 in CWX.
    all: assert (CWX' : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) X 16)
           by (eapply client_wrange_sp_mono; [| exact CWX]; clear - LOS LOSP; lia).
    all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0x9f1d4) _ _ ?mx _] =>
           lazymatch goal with MU5 : munch ?W5 ?m0 mx, WM5 : wmono _ ?m0 mx, MI5 : mem_inv _ mx, OX5 : aobj _ _ _ mx X 16 |- _ =>
             pose proof (munch_weaken W5 [(X, X + 16)] m0 mx ltac:(intros x Hx; cbn [outside] in Hx |- *; lia) MU5) as MUX;
             assert (HH5 : HM asegs R HIA hc LBc LF mx)
               by (eapply (hm_munch asegs R HIA hc LBc LF [(X, X + 16)] m0 mx HHc MUX WM5);
                   apply Forall_cons; [cbn [fst snd]; apply w_writable_of_client_wrange; replace (X + 16 - X) with 16 by (clear; lia); exact CWX'| apply Forall_nil]);
             first
               [ match goal with H : rw_cells asegs mx X [C8 _; C2 (Z_to_bv 64 1); _; _] |- _ =>
                   pose proof (xa_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ 1 J MUX WM5 MI5 H (or_introl eq_refl) HH5 OX5) as J5 end
               | match goal with H : rw_cells asegs mx X [C8 ?pp; C2 (Z_to_bv 64 ?a); ?nn; ?pd] |- _ =>
                   pose proof (rw_cells_C2_congr asegs mx X [C8 pp] a (md_sg dA * md_sg dB) [nn; pd] H
                                 ltac:(clear - SGA SGB; destruct SGA as [-> | ->]; destruct SGB as [-> | ->]; vm_compute; reflexivity)) as CX5;
                   pose proof (xa_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ (md_sg dA * md_sg dB) J MUX WM5 MI5 CX5
                                 ltac:(clear - SGA SGB; destruct SGA as [-> | ->]; destruct SGB as [-> | ->]; first [cbn; tauto| lia]) HH5 OX5) as J5 end ]
           end end.
    all: pose proof KCL as KCLu; unfold KCLB_stmt in KCLu.
    all: lazymatch type of J5 with XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mx ?d => mb_apply (KCLu v f hc LBc mx d 0) end.
    all: first [exact J5 | (left; reflexivity) | exact BV | exact BF | exact SZ].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "02?0@L10351591498.3  L10374722182.2  L11073781088.4  L11085642677.188L122581036.14   L124765098.12   L124779541.6    L124779668.6    L1356673058.3   L1356673187.5   L1358740507.11  L13705671073.0  L14282253968.188L14286118981.4  L15968070499.11 L15970133850.4  L15970133979.4  L22706232213.5  L22710623552.185L23597190194.10 L23597200140.4  L23597200269.3  L23599333300.11 L26056220436.5  L26056282294.166L2660745077.5   L2747762755.11  L2749760634.4   L2749760763.4   L2804139892.8   L2804305022.7   L2814379021.6   L2814627752.13  L2816622997.6   L2816623376.6   L2816623505.6   L2816637998.11  L30031639647.186L30031639647.187L30044549770.3  L30544818878.11 L30546951686.3  L30546951815.5  L31742545515.188L31755978942.4  L31944159078.8  L31946089529.188L31956702268.11 L31956702268.12 L31956708098.5  L31956708227.6  L31957300856.3  L31958837178.13 L31958952092.7  L34861500360.2  L35629214198.1  L35667858935.6  L35668120833.7  L36793445084.188L36807145629.3  L38250484404.187L38558082328.187L38558082328.194L38569812941.1  L39436416899.12 L39733042933.4  L41887908774.4  L41887908774.8  L43877802600.187L44082271972.1  L44146116325.15 L44148312669.7  L44148312796.7  L44148323683.13 L44152409657.9  L44423159706.3  L45272757598.3  L45272757727.4  L46223120590.7  L46732241046.2  L4732976287.11  L4735029017.10  L4735037479.3   L4735037606.4   L49112248975.11 L49112938457.4  L49114315954.5  L49114316343.5  L49114316470.4  L49116803340.188L49116803340.189L50252514442.7  L53442558319.10 L53643321043.3  L53657825229.7  L53657886955.13 L53660078957.11 L53660078957.12 L53660085331.6  L53660085458.5  L53660545321.3  L53662311272.188L53664180279.8  L56473130795.194L56828860791.9  L56828863692.4  L56828864073.4  L56828864200.4  L56830845268.4  L56830864113.11 L57628690880.192L57718672844.3  L58655655838.1  L60098763854.3  L60111543915.194L60570960132.185L60570960132.189L60576273221.2  L60600074326.4  L60600074455.5  L60600074963.5  L60601452984.4  L60602076398.11 L60614889325.188L62232297790.187L62232297790.194L63255625131.7  L63259916622.4  L63259916751.4  L63261914487.12 L63719128318.12 L6413260598.5   L65415404733.13 L65427888216.9  L65427888345.9  L65427892199.15 L65427892199.16 L65430082657.15 L66151427842.16 L66151427842.17 L6958572106.5   L6958572235.5   L6960639603.11  00000900A00B01U01V01W01X01Y01Z01[01\01]03;03<03=03>03?03@04H04I04J04K04L04a05[05l06<06=06>06?06P06Q06R06S06T06U06V06W06X06Y06Z06[06\07o08008109O09P09Q09R09S09T09U09d09l0:10:E0:]0<80<90<h0=T0>F0>K0>c0>o0?;0?G0@:0@?0@@0@A0@B0@C0@D0@O0@X0@Y0@m0A50A60A70A80A90A:0A;0A<0A=0A>0B`0Ba0C60CH0CQ0C`0Ca0Cb0Cc0Cd0Ce0Cf0ED0EE0F]0F^0F_0F`0Fa0Fo0G00HL0HU0HZ0Hd0I_0I`0Ia0Ib0Ic0Id0Ie0If0Ig0KI0L<0M20M30M40M50M60MS0Ma0Mb0Mc0Md0Me0Mf0Mg0NK0NL0NM0NN0NOS2dA1i2HIS3spv2loFS1R3spv3xs02dA2dB2lo4SLO21i1j3dXc2c02c83c163c243c323c403c482fl2HN5NEEDR3LOS4ALO'2PCFFFFFFFSS1R3HIA2LF3spv1X3xs02dA2dB2lo1i1j2hc3LBc3dXc2c02c83c163c243c323c403c482fl2HN3x143XPc3x155POST0FFFFFS1R3spv3xs02dA2dB2lo1i1j3dXc2c02c83c163c243c323c403c482fl2HN3LOS4ALO'2PCFFFFS3spv2lo3LO04LOSP3SPRS3spv3xs02dA2dB3dXc2c02c83c163c243c323c403c482fl4SP644SPR'S1R3HIA1h3spv3TOPS1i1j3dXc2HN3NR1FFFS3spv2lo3dXc4XLScFFFFFFFFFFFFS1R3spv3xs02dA2dB2lo4SLO21i1j3dXc2c02c83c163c243c323c403c482fl2HN5NEEDR3LOS4ALO'2PCFFS1R3HIA2LF3spv3xs02dA2dB2lo1i1j2hc3LBc3dXc2c02c83c163c243c323c403c482fl3x144LENA3ALS3x155POST0FFFFFFS3spv2dA2lo3ALSS3spv2loS3spvS1R3HIA1h3spv2lo3XSCS1R3HIA1h3spv2lo3TOP3HTqS1R3HIA2LF3spv1X3xs02dA2dB2lo1i1j2hc3LBc3dXc2c02c83c163c243c323c403c482fl3DSX3x143x155POST0FS3xs02dA2dB2lo3dXc2c02c83c163c243c323c403c482flS3xs02dA2dB3dXc2c02c83c163c243c323c403c482flS3spv1X3xs02dA2dB3dXc2c02c83c163c243c323c403c482flS3dXcS3spv2lo1i1j3dXc2HN1a2NOS1i1j3dXc2HNS1i1j3dXc2HNS1i1j3dXc2HNS3spv3xs02dA2dB2lo3dXc2c02c83c163c243c323c403c482flS3spvFFFFFS3spv1X3XSDS2dB1j2HJFS1R3spv2lo4SLO24NRAmS3spv2loFFFFFFFFFS1R3HIA2LF3spv3xs02dA2dB2lo1i1j2hc3LBc3dXc2c02c83c163c243c323c403c482fl2HN3x144LENB4BSEP3x155POST0FS2dA2dB1i1j3dXc2HI2HJS1X1i1j3dXc2HN3XPcS2dA1i2HIS3spv2dB2lo3BLSFFFFFFS1R3HIA2LF3spv3xs02dA2dB2lo1i1j2hc3LBc3dXc2c02c83c163c243c323c403c482fl3x144LENB3BLS3x155POST0FS1R3HIA1h3spv1X3xs02dA2dB2lo2hc3dXc2c02c83c163c243c323c403c482fl3TOP2X02A02B02P03HT13SPRFFFFS1R3dXc2PC3ACVFS1R3HIA2LF3spv3xs02dA2dB2lo1i1j2hc3LBc3dXc2c02c83c163c243c323c403c482fl3x143x155POST03x162H0S2dB1j2HJS3spvS1R2lo3LOSS1R3spv1X3xs02dA2dB2lo3dXc2c02c83c163c243c323c403c482fl3LOSFFFFFFFFS1R3HIA2LF3spv3xs02dA2dB2lo1i1j2hc3LBc3dXc2c02c83c163c243c323c403c482fl2HN3x144LENA4ASEP3x155POST0S3xs02dA2dB1i1j3dXc2c02c83c163c243c323c403c482fl2HNS3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c243c323c403c482flFFFFS3spv2lo1i1j3dXc2HN4LOSP4XLScS3spv1X2lo3DSXFFFFFFS3dXc2r04XPAL1q1r1H2H02q02H43spv3SPAFFFF".
  Lemma mb_CORE : forall (i j v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
           (c0 c8 c16 c24 c32 c40 c48 fl : word)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 : word),
      XJA asegs R HIA h LB LF m dX spv lo 80
        (mm_frb c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dB + 8)) fl (Z_to_bv 64 (md_addr dA + 8))) [] v f hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dA hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dB hc LBc mc dXc ->
      md_own dXc = LHeap ->
      0 <= i <= md_n dA -> 0 <= j <= md_n dB -> i + j <= md_n dXc ->
      v <= mul_mid_PHI dA dB -> f <= mul_mid_FR d1 + fr_charge 0 -> md_n dXc <= SZB ->
      aevtA asegs (KF asegs R HIA hc mo) POST
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned spv + -80)) gp tp xt0 xt1 xt2 spe (Z_to_bv 64 (bv_unsigned spv + -80))
                 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                 xs2 (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (al_sb AL + Z.shiftr (md_addr dB) 3)) (Z_to_bv 64 (- j)) (Z_to_bv 64 (md_addr dB))
                 (Z_to_bv 64 (md_addr dA)) xs8 (Z_to_bv 64 (al_sb AL + Z.shiftr (md_addr dA) 3)) (Z_to_bv 64 i) xs11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x9f304) fc None mc (seg_rom asegs)).
  Proof.
    intros i j v f hc LBc mc dXc c0 c8 c16 c24 c32 c40 c48 fl xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 J RA RB EO HI HJ HN BV BF SZ.
    pose proof (JC c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dB + 8)) fl (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 80 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    destruct (mb_view dA _ _ _ _ _ _ _ J RA NXA) as (CEA & OEA & SGA & A0 & A16 & AAL).
    destruct (mb_view dB _ _ _ _ _ _ _ J RB NXB) as (CEB & OEB & SGB & B0 & B16 & BAL).
    destruct (mb_limbs dA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i J RA NXA EO HI) as (ABY & LENA & ASEP & PA4 & PAZ & A64 & ALS & OAL).
    destruct (mb_limbs dB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j J RB NXB EO HJ) as (BBY & LENB & BSEP & PB4 & PBZ & B64 & BLS & OBL).
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    unfold mpi_cells in CX1. cbn [md_addr md_pad] in CX1.
    ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1.
    pose proof (xa_aobjX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as OX1. cbn [md_addr] in OX1.
    pose proof (xa_XLS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as XLS1. pose proof (XLS1 ltac:(rewrite EO; discriminate)) as XLSc. clear XLS1.
    pose proof (xa_XP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as XP1. pose proof (XP1 EO) as XPc. clear XP1. cbn [md_addr] in XPc.
    pose proof (xa_top _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HT1.
    pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HH1. cbn [app] in HH1.
    pose proof (alloc_ceiling_val R) as ACV. pose proof (arl_need_rt_amem R) as NRAm.
    pose proof (xa_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HPX1.
    assert (XSLc : rw_cells asegs mc (bv_unsigned spv + 40) [C8 (Z_to_bv 64 X)]).
    { eapply presA_rw_cells; [exact HPX1| exact XSL| apply client_range_stack; clear; lia|].
      replace (Z.of_nat (cells_size [C8 (Z_to_bv 64 X)])) with 8 by reflexivity. cbn [disjoint_from md_addr]. split; [| exact I].
      clear - XSD; lia. }
    clear HPX1.
    assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) (md_p dXc) (4 * (i + j)))
      by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear - HN HI HJ; lia]).
    mb_base hc J. mb_frame J. mb_scs hc J LOS TOP HH.
    assert (SCS8 : crange (hcs asegs R HIA hc) lo (bv_unsigned spv + 48 - lo))
      by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; clear - XSC; lia]).
    pose proof (bv_unsigned_in_range 64 spv) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (SPR' : 0 <= bv_unsigned spv + -80 < 2^64) by (clear - SPR LOSP LO0; lia).
    lx_pre. lx_run_tac (PLAN [0xa52a8; 0x9f3b0] [] 40%N). lx_tree.
    all: try lx_same_mem.
    repeat match goal with H : munch _ _ mc |- _ => clear H end.
    repeat match goal with H : wmono _ _ mc |- _ => clear H end.
    pose proof CMUL as SPC. unfold mpi_core_mul_stmtA, A_MPI_CORE_MUL in SPC.
    pose proof (munch_refl [(md_p dXc, md_p dXc + 4 * (i + j)); (lo, bv_unsigned spv + -80)] mc) as MU0.
    pose proof (wmono_refl asegs mc) as WM0.
    acallxA_sp (bv_unsigned spv + -80)
      (eapply SPC with (h := hc) (LB := LBc) (LF := LF) (X := md_p dXc) (A := md_p dA) (an := i) (B := md_p dB) (bn := j) (lo := lo)
                       (xs := md_limbs dXc) (ys := md_limbs dA) (zs := md_limbs dB);
       rewrite ?(unsigned_lit (bv_unsigned spv + -80)) by exact SPR';
       try eassumption; try reflexivity;
       first [ clear - HI; lia
             | clear - HJ; lia
             | clear - HI HJ NRA NRB HN NR1; lia
             | rewrite LEN1; clear - HN; lia
             | rewrite LENA; clear - HI; lia
             | rewrite LENB; clear - HJ; lia
             | rewrite LENA, LEN1; exact ASEP
             | rewrite LENB, LEN1; exact BSEP
             | clear - XPAL; Z.div_mod_to_equations; lia
             | rewrite LEN1; clear - PC ACV; lia
             | rewrite LENA; exact A64
             | rewrite LENB; exact B64
             | unfold MPI_CORE_MUL_STACK_A; clear - SLO2 NEEDR NRAm LOS; lia
             | rewrite HT1; clear - TOP; lia
             | clear - SPA; Z.div_mod_to_equations; lia
             | rewrite LEN1; clear - XLSc SLO2 NEEDR; lia
             | rewrite LENA; clear - ALS SLO2 NEEDR; lia
             | rewrite LENB; clear - BLS SLO2 NEEDR; lia
             | exact CWP
             | eapply aobj_sub; [exact OP| clear; lia| clear - HN HI HJ; lia]
             | rewrite unsigned_lit by lia; reflexivity
             | f_equal; lia ]).
    clear SPC.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
    match goal with H : stk asegs m6 lo (bv_unsigned spv + -80) |- _ => rename H into ST6 end.
    match goal with H : u32arr asegs m6 (md_p dXc) ?l, H2 : length ?l = length (md_limbs dXc) |- _ => rename H into XARR6; rename H2 into LEN6; rename l into xs6 end.
    match goal with H : HM asegs R HIA hc LBc LF m6 |- _ => rename H into HH6 end.
    match goal with H : munch _ mc m6 |- _ => rename H into MU6 end.
    match goal with H : wmono asegs mc m6 |- _ => rename H into WM6 end.
    assert (ST6' : stk asegs m6 lo (bv_unsigned spv - 80)) by (replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) by (clear; lia); exact ST6).
    assert (HW6 : forall a, ~ outside [(md_p dXc, md_p dXc + 4 * (i + j)); (lo, bv_unsigned spv + -80)] a ->
                  (md_own dXc = LHeap /\ md_p dXc <= a < md_p dXc + 4 * md_n dXc) \/ lo <= a < bv_unsigned spv - 80).
    { intros a NO. cbn [outside] in NO.
      assert (D : md_p dXc <= a < md_p dXc + 4 * md_n dXc \/ lo <= a < bv_unsigned spv - 80) by (clear - NO HN HI HJ; lia).
      destruct D as [D|D]; [left; split; [exact EO| exact D]| right; exact D]. }
    pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ _ m6 xs6 J MU6 WM6 MI6 ST6' HH6 HW6
                  ltac:(cbn [disjoint_from]; split; [clear - XLSc HN HI HJ LOSP; lia| split; [clear; lia| exact I]])
                  ltac:(cbn [disjoint_from md_addr]; split; [clear - XPc HN HI HJ; lia| split; [clear - DSX LOSP; lia| exact I]]) XARR6 LEN6) as J6.
    pose proof (rideA_xl_munch R HIA h LB LF m dX spv lo 80 _ JCc dA _ _ _ _ _ _ (md_p dXc) (md_p dXc + 4 * (i + j)) xs6 m6 (bv_unsigned spv + -80) J RA EO
                  ltac:(clear; lia) ltac:(clear - HI HJ; lia) ltac:(clear - HN; lia) ltac:(clear; lia) MU6 WM6) as RA6.
    pose proof (rideA_xl_munch R HIA h LB LF m dX spv lo 80 _ JCc dB _ _ _ _ _ _ (md_p dXc) (md_p dXc + 4 * (i + j)) xs6 m6 (bv_unsigned spv + -80) J RB EO
                  ltac:(clear; lia) ltac:(clear - HI HJ; lia) ltac:(clear - HN; lia) ltac:(clear; lia) MU6 WM6) as RB6.
    mb_apply (mb_SIGN v f hc LBc m6 (mkMPD (md_addr dXc) (md_sg dXc) (md_n dXc) (md_p dXc) xs6 (md_pad dXc) (md_own dXc)) c0 c8 c16 c24 c32 c40 c48 fl).
    all: first [exact J6 | exact RA6 | exact RB6 | exact BV | exact BF | exact SZ].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00e0@L11868453103.160L11966851360.160L17767404552.196L19282607183.167L19282607437.174L19282607564.172L19286836073.165L21025220948.167L22744573761.162L26056220436.156L31610506949.167L31610507078.172L31610507207.174L31623148003.165L35626874637.197L42243570962.160L42330923874.199L42332625762.200L42343130104.198L44146134245.160L44990861757.174L46155825223.196L46155825731.175L46155825858.173L46155825858.174L51779725399.173L51779725399.174L51779725526.175L51779725780.168L51779726034.196L51783866098.166L51783866098.167L51783866259.190L58655890651.160L59308579152.174L59314873579.2  L59314873579.3  L59321214965.167L59450053136.196L61486657911.160L61958282297.198L66151427842.16 L6818945001.168 L6823094479.167 L6823094702.190 L68707055134.160L722174397.165  L734756507.167  L734756632.172  L734756761.174  L7386780486.198 L8022072597.196 L8034705492.190 00000b02303>03?03@03A03B03C04705S05T05U05V05W06I07E08?0990:30;?0<G0<H0<I0<J0<K0<L0<M0<N0<O0<P0<Q0<R0<S0=E0=F0=G0=H0=I0>;0>m0?_0@:0@;0@<0@=0AS0AT0AU0AV0AW0BI0CC0D=S3spv1X3xs02dA2dB3dXc2c02c83c163c243c323c403c482flS1R3HIA1h3spv1X3xs02dA2dB3BUD1v2hc3dXc2c02c83c163c243c323c403c482fl2BV2X03HV13SPRS3spv1X2nX3xs02dA2dB3dXc2c02c83c163c243c323c403c482fl2SZ2X03LEN3SPR3dX23EN2FFFFFS3spv1X3xs02dA2dB3dXc2c02c83c163c243c323c403c482fl1QS1R3spv1X3xs02dA2dB2lo4SLO23dXc2c02c83c163c243c323c403c482fl5NEEDR3LOS4SP644ALO'4ACP'2X03SPRFFFFS3spv1X3xs02dA2dB3dXc2c02c83c163c243c323c403c482flS1R3spv1X3xs02dA2dB2lo4SLO23dXc2c02c83c163c243c323c403c482flS3spv1X3xs02dA2dB2lo3dXc2c02c83c163c243c323c403c482fl4LOSPS3spv1X3xs02dA2dB2lo3dXc2c02c83c163c243c323c403c482fl4LOSPS3spv1X3xs02dA2dB2lo3dXc2c02c83c163c243c323c403c482fl4LOSPS1R3HIA1h3spv1X3xs02dA2dB2hc3dXc2c02c83c163c243c323c403c482fl3TOP2X03HT13SPRS3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c243c323c403c482fl2HN2X03SPR3dX23EN2FFFFFFFFFFFFS3spv1X3xs02dA2dB3dXc2c02c83c163c243c323c403c482flFFFFS3spv1X3xs02dA2dB3dXc2c02c83c163c243c323c403c482flS3spv1X3xs02dA2dB3dXc2c02c83c163c243c323c403c482flS3spv1X3xs02dA2dB3dXc2c02c83c163c243c323c403c482flS3spv2r03SPA1q1r1H2H02q02H4FFFS1R3HIA1h3spv1X3xs02dA2dB2d14BUDF1f2hc3dXc2c02c83c163c243c323c403c482fl2BF2X04HFR13SPRFFFFS3spv1X3xs02dA2dB3dXc2c02c83c163c243c323c403c482flS3spv1X3xs02dA2dB2d11f3dXc2c02c83c163c243c323c403c482fl2BFS3spv1X3xs02dA2dB2d11f3dXc2c02c83c163c243c323c403c482fl2BF".
  Lemma mb_LSETP : forall (i j v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
           (c0 c8 c16 c24 c32 c40 c48 fl : word)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs11 xt3 xt4 xt5 xt6 : word),
      XJA asegs R HIA h LB LF m dX spv lo 80
        (mm_frb c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dB + 8)) fl (Z_to_bv 64 (md_addr dA + 8))) [] v f hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dA hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dB hc LBc mc dXc ->
      uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned spe) (bv_unsigned spv) d1 ->
      0 <= i <= md_n dA -> 0 <= j <= md_n dB -> i + j <= md_n dXc ->
      v + grow_PHI 1 <= mul_mid_PHI dA dB -> f <= mul_mid_FR d1 -> md_n dXc <= SZB ->
      aevtA asegs (KF asegs R HIA hc mo) POST
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned spv + -80)) gp tp xt0 xt1 xt2 spe (Z_to_bv 64 (bv_unsigned spv + -80))
                 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 X) xa7
                 xs2 (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (al_sb AL + Z.shiftr (md_addr dB) 3)) (Z_to_bv 64 (- j)) (Z_to_bv 64 (md_addr dB))
                 (Z_to_bv 64 (md_addr dA)) xs8 (Z_to_bv 64 (al_sb AL + Z.shiftr (md_addr dA) 3)) (Z_to_bv 64 i) xs11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x9f1c0) fc None mc (seg_rom asegs)).
  Proof.
    intros i j v f hc LBc mc dXc c0 c8 c16 c24 c32 c40 c48 fl xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs11 xt3 xt4 xt5 xt6 J RA RB UW HI HJ HN BV BF SZ.
    pose proof (JC c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dB + 8)) fl (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 80 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J as JX. pose proof JX as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in AD1, OX1, XP1.
    pose proof (xa_cwX _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J) as CWX. rewrite <- HT1 in CWX.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (hcs_ok asegs R HIA hc) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (art_alwf asegs R HIA) as ALWF'.
    pose proof (bv_unsigned_in_range 64 spv) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (SPR' : 0 <= bv_unsigned spv + -80 < 2^64) by lia.
    lx_pre. lx_run_tac (PLAN [0x9c204; 0x9f3b0] [] 10%N). lx_tree.
    all: try lxu_chk_leaves 0x9f3b0.
    all: try lx_same_mem.
    pose proof LSET as SPc. unfold mpi_lset_stmtA, mpi_xop_stmtA, A_MPI_LSET in SPc.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SPc with (h := hc) (LB := LBc) (LF := LF) (dX := dXc) (v := 0) (lo := lo) (d := d1);
        rewrite ?(unsigned_lit (bv_unsigned spv + -80)) by exact SPR'; rewrite ?AD1; cbv beta;
        first [ exact HH1 | exact HK1 | exact MX1 | exact NS1 | exact MI1 | exact LOS | exact TPV | reflexivity
              | lazymatch goal with
                | |- mpd_writableA _ _ _ _ _ dXc => split; [rewrite AD1; eapply client_wrange_sp_mono; [| exact CWX]; lia| rewrite AD1; exact XP1]
                | |- md_own dXc <> LNull -> _ => intros NN; destruct (XLS1 NN) as [Q|Q]; [left; exact Q| right; lia]
                | |- stk _ _ _ _ => replace (bv_unsigned spv + -80) with (bv_unsigned spv - 80) by lia; exact ST1
                | |- (bv_unsigned spv + -80) mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => rewrite unsigned_lit by lia; reflexivity
                | |- mpd_aobjA _ _ _ _ dXc => split; [rewrite AD1; exact OX1| intros E; exfalso; exact (NS1 E)]
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold mul_mid_PHI, grow_PHI, AVOL_CALL in *; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold lset_FR, mul_mid_FR, calls_FR, fr_charge in *; lia
                | |- uwc _ _ _ _ _ _ _ => rewrite HS1; eapply uwc_floor; [exact UW| lia]
                | |- uw_obj _ _ _ _ => exact XUW
                | |- _ => lia
                end
              | match goal with |- ?g => idtac "LSET-PRE-LEFT:" g end ]. }
    intros ms' mo' dd_H. ddestruct dd_H as (mo1 & [HK1 MF1] & PO). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned spv + -80)) in ST2, HP2 by exact SPR'. rewrite AD1 in HP2.
    replace (ret_pc (Z_to_bv 64 0x9f1cc)) with (Z_to_bv 64 0x9f1cc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (mb_lset_keep _ _ _ _ _ CR) as BK.
    assert (ST2' : stk asegs m2 lo (bv_unsigned spv - 80)) by (replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) by lia; exact ST2).
    pose proof (xa_call asegs R HIA h LB LF m dX spv lo 80 _ JCc _ _ _ _ _ _ m2 h2 LB2 dX2 (bv_unsigned spv + -80) (grow_PHI 1) (lset_FR d1) J ltac:(lia)
                  ltac:(unfold grow_PHI, AVOL_CALL; lia) ltac:(unfold lset_FR, calls_FR, fr_charge; lia) MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
    pose proof (mb_ride_call dA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 h2 LB2 dX2 (bv_unsigned spv + -80) J RA ltac:(lia) MI2 HP2 HCS2 HH2 MX2 OUT2 FRA2) as RA1.
    pose proof (mb_ride_call dB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 h2 LB2 dX2 (bv_unsigned spv + -80) J RB ltac:(lia) MI2 HP2 HCS2 HH2 MX2 OUT2 FRA2) as RB1.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    destruct CR as [[(R0 & EN2 & EO2 & _ & _ & EP2)|(R16 & ED2)] [CA2 CF2]].
    - subst r.
      lx_pre. lx_run_tac (PLAN [0x9f304; 0x9f1d4; 0x9f3b0] [] 20%N). lx_tree.
      all: try lx_same_mem.
      all: try lazymatch goal with
           | |- context [MS _ _ (Z_to_bv 64 0x9f304) _ _ _ _] => mb_apply (mb_CORE i j (v + grow_PHI 1) (f + lset_FR d1) h2 LB2 m2 dX2); mb_budget
           end.
      all: try (unfold mul_mid_SZ in *; lia).
    - subst r dX2. unfold MBEDTLS_ERR_MPI_ALLOC_FAILED.
      lx_pre. lx_run_tac (PLAN [0x9f304; 0x9f1d4; 0x9f3b0] [] 20%N). lx_tree.
      all: try lx_same_mem.
      all: try lazymatch goal with
           | |- context [MS _ _ (Z_to_bv 64 0x9f1d4) _ _ _ _] => let KCLu := fresh "KCLu" in pose proof KCL as KCLu; unfold KCLB_stmt in KCLu; mb_apply (KCLu (v + grow_PHI 1) (f + lset_FR d1) h2 LB2 m2 dXc (-16)); mb_budget
           end.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L35629214198.1  L35668120833.8  L51087234226.179L52437841502.184L57628700040.176L60098763854.3  L62035228629.182L996370269.182  00000500P01_03<03o04905J06YS3spvS1R3HIA1h3spv2lo2hd3TOP3HTqS1R3spv1X3xs02dA2dB2lo4SLO23cnt2An2ys2c02c83c163c322fl5NEEDR3LOS4ALO'2X04Hfr01HS1R3HIA1h3spv1X3xs02dA2dB2lo4SLO23cnt2An2ys2c02c83c163c322fl5NEEDR3LOS4ALO'2X04Hfr01H2XL1a2HaS1R3spv1X3xs02dA2dB3cnt2An2ys2c02c83c163c322fl1x2HxS1R2lo3LOSS1R3spv1X3xs02dA2dB2lo4SLO23cnt2An2ys2c02c83c163c322fl5NEEDR3LOS4SP642X03X164Hfr0S1R3spv1X3xs02dA2dB2lo4SLO23cnt2An2ys2c02c83c163c322fl5NEEDR3LOS4ALO'2X04Hfr01H".
  Lemma mb_GFIN : forall (i j cnt v f : Z) (hd : HST asegs R HIA) (LBd : list blk) (An : Z) (ys : list word) (me : mem) (dXc : mpd)
           (c0 c8 c16 c32 fl : word)
           (xra xt0 xt1 xt2 xa1 xa4 xa5 xa7 xt3 xt4 xt5 xt6 : word),
      XDA asegs R HIA h LB LF m dX spv lo 80
        (mm_frb c0 c8 c16 (Z_to_bv 64 (X + 10)) c32 (Z_to_bv 64 (al_sb AL + Z.shiftr (X + 10) 3)) (Z_to_bv 64 cnt)
                (Z_to_bv 64 (md_addr dB + 8)) fl (Z_to_bv 64 (md_addr dA + 8))) v f hd LBd An cnt ys me dXc ->
      rideA R HIA LB LF m dX spv lo dA hd LBd me dXc ->
      rideA R HIA LB LF m dX spv lo dB hd LBd me dXc ->
      uwc asegs me (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned spe) (bv_unsigned spv) d1 ->
      0 <= i <= md_n dA -> 0 <= j <= md_n dB -> i + j <= cnt ->
      v + grow_PHI 1 <= mul_mid_PHI dA dB -> f <= mul_mid_FR d1 -> cnt <= SZB ->
      aevtA asegs (KF asegs R HIA hd mo) POST
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned spv + -80)) gp tp xt0 xt1 xt2 spe (Z_to_bv 64 (bv_unsigned spv + -80))
                 (Z_to_bv 64 An) xa1 (Z_to_bv 64 cnt) (Z_to_bv 64 (al_sb AL + Z.shiftr (X + 10) 3)) xa4 xa5 (Z_to_bv 64 X) xa7
                 xs2 (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (al_sb AL + Z.shiftr (md_addr dB) 3)) (Z_to_bv 64 (- j)) (Z_to_bv 64 (md_addr dB))
                 (Z_to_bv 64 (md_addr dA)) xs8 (Z_to_bv 64 (al_sb AL + Z.shiftr (md_addr dA) 3)) (Z_to_bv 64 i) (Z_to_bv 64 (al_sb AL + Z.shiftr X 3)) xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x9f1a8) fc None me (seg_rom asegs)).
  Proof.
    intros i j cnt v f hd LBd An ys me dXc c0 c8 c16 c32 fl xra xt0 xt1 xt2 xa1 xa4 xa5 xa7 xt3 xt4 xt5 xt6 D RA RB UW HI HJ HN BV BF SZ.
    pose proof (JC c0 c8 c16 (Z_to_bv 64 (X + 10)) c32 (Z_to_bv 64 (al_sb AL + Z.shiftr (X + 10) 3)) (Z_to_bv 64 cnt) (Z_to_bv 64 (md_addr dB + 8)) fl (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 80 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    pose proof D as [DMI DST DFR DHM DHT DHS DHF DHCS DHV DHFR DCX DSG DSUB DKEEP DGONE DNEW DAPART DARR DLEN DCNT DXS DPRES DFRESH DAL DOX DLO DNM].
    cbn [md_addr md_pad] in DCX, DOX. unfold mpi_cells in DCX.
    pose proof (xda_cwX _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ _ _ D) as CW5. cbn [md_addr] in CW5.
    pose proof (hcs_ok asegs R HIA hd) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (art_alwf asegs R HIA) as ALWF'.
    pose proof (AIh_laws asegs R HIA hd) as LAWS. pose proof (KF_kinv asegs R HIA hd mo) as KINV.
    pose proof DFR as FR. pose proof DST as ST. unfold mm_frb in FR.
    replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) in FR, ST by (clear; lia).
    pose proof (hcs_stack asegs R HIA hd) as SCS0. pose proof (hm_top asegs R HIA hd _ LF me DHM) as HTq.
    assert (SCS : crange (hcs asegs R HIA hd) lo (bv_unsigned spv - lo))
      by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite DHT in HTq; clear - HTq TOP; lia]).
    lx_pre. lx_run_tac (PLAN [0x9f1c0; 0x9f3b0] [(0x9f1ac, DJoin)] 30%N). lx_tree.
    all: try lxu_chk_leaves 0x9f3b0.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => rename mx into m5 end.
    match goal with H : munch _ me m5 |- _ => rename H into MU50 end.
    match goal with H : wmono _ me m5 |- _ => rename H into WM5 end.
    match goal with H : mem_inv _ m5 |- _ => rename H into MI5 end.
    assert (MU5 : munch [(X, X + 16)] me m5) by (eapply munch_weaken; [| exact MU50]; intros x Hx; cbn [outside] in Hx |- *; lia).
    assert (OX5 : aobj asegs AL (hcs asegs R HIA hd) m5 X 16) by eassumption.
    assert (CX5 : rw_cells asegs m5 X (mpi_cells An (Z_to_bv 64 (md_sg dXc)) cnt padX)) by (unfold mpi_cells; eassumption).
    assert (HM5 : HM asegs R HIA hd ((An, 4 * cnt) :: LBd) LF m5).
    { eapply (hm_munch asegs R HIA hd _ LF [(X, X + 16)] me m5 DHM MU5 WM5).
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. unfold hm_writable. left.
      rewrite DHT.
      assert (CW5' : client_wrange (arl_L R) (((An, 4 * cnt) :: LBd) ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) X 16)
        by (eapply client_wrange_sp_mono; [| exact CW5]; lia).
      exact (CW5' a Ha). }
    pose proof (xda_finish _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ _ _ _ D MU5 WM5 MI5 CX5 HM5 OX5) as J5.
    pose proof (rideA_finish R HIA h LB LF m dX spv lo 80 _ JCc dA _ _ _ _ _ _ _ _ _ _ D RA MU5 WM5) as RA5.
    pose proof (rideA_finish R HIA h LB LF m dX spv lo 80 _ JCc dB _ _ _ _ _ _ _ _ _ _ D RB MU5 WM5) as RB5.
    assert (UW5 : uwc asegs m5 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned spe) (bv_unsigned spv) d1).
    { destruct XUW as [[XL _]|D28]; [| apply uwc_cap; exact D28].
      eapply uwc_munch; [exact UW| exact MU5| lia| apply hstkhi_le64; lia|].
      intros a Ha. cbn [outside]. split; [lia| exact I]. }
    mb_apply (mb_LSETP i j v f hd ((An, 4 * cnt) :: LBd) m5 (mkMPD (md_addr dX) (md_sg dXc) cnt An ys (md_pad dX) LHeap)).
    all: try eassumption.
    all: mb_budget.
    all: try (cbn [md_n]; lia).
    all: try (unfold mul_mid_SZ in *; cbn [md_n]; lia).
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00G0@L11870765557.224L1609858923.193 L22196713738.13 L22198845578.193L23500467423.170L26056220436.169L2660365520.193 L26841176882.227L28244954934.222L33560573857.12 L33562611233.193L34423215124.193L35628807604.222L35629214198.1  L35668120833.8  L521871523.193  L58176319561.229L58655890653.193L60098763854.3  L61442513679.193L62037225709.227L63261966193.193L994173029.227  00000d02=02>02?03?04V05T06H07<07=07>08:08n09309Q0:o0<X0=L0=V0>a0@:0AN0BFS1R3spv1X3xs02dA2dB3cnt2An2ys2nc2pc2xs2c02c82fl4ZLENS1R3HIA1h3spv1X3xs02dA2dB3BUD3cnt1v2hc2An2ys2nc2pc2xs2c02c82fl2BV2X02P03HV03SPR4Hfr04ZLENFFS1R3spv1X3xs02dA2dB3cnt2An2ys2nc2pc2xs2c02c82fl2X02N12P03P473SPRS1R3spv1X3xs02dA2dB2lo4SLO23cnt2An2ys2pc2xs2c02c82fl5NEEDR3LOS4SP644ALO'4ACP'2X02P03SPRS1R3HIA1h3spv1X3xs02dA2dB3cnt2An2ys2nc2pc2xs2c02c82fl3TOP4ZLENS1R3spv1X3xs02dA2dB3cnt2An2ys2nc2pc2xs2c02c82fl4ZLENS1R3spv1X3xs02dA2dB3cnt2An2ys2nc2pc2xs2c02c82fl4ZLENFFS1R3spv1X3xs02dA2dB2lo4SLO23cnt2An2ys2nc2pc2xs2c02c82fl4ZLENS1R3spv1X3xs02dA2dB3cnt2An2ys2nc2pc2xs2c02c82fl4ZLENS3spvS1R3HIA1h3spv2lo2hc3TOP3HTq2h4S1R3HIA1h3spv1X3xs02dA2dB2d14BUDF3cnt1f2hc2An2ys2nc2pc2xs2c02c82fl2BF2X02P04HFR03SPR4Hfr04ZLENS1R3HIA3spv1X3xs02dA2dB2lo4SLO23cnt2hc2An2ys2nc2pc2xs2c02c82fl5NEEDR3LOS4ALO'2X02P02PC3SPR4Hfr04ZLEN1a2HaS1R3spv1X3xs02dA2dB3cnt2An2ys2nc2pc2xs2c02c82fl4ZLENS1R2lo3LOSS1R3spv1X3xs02dA2dB3cnt2An2ys2nc2pc2xs2c02c82fl2X02P04Fcnt3SPR4Hfr04ZLEN2ZBS1R3spv1X3xs02dA2dB2lo4SLO23cnt2An2ys2nc2pc2xs2c02c82fl5NEEDR3LOS2X03X162P03SPR4Hfr04ZLENS1R3spv1X3xs02dA2dB3cnt2An2ys2nc2pc2xs2c02c82fl3SPA2X04LEN12N12P03SPR4SPR'4Hfr04ZLENS1R3spv1X3xs02dA2dB3cnt2An2ys2nc2pc2xs2c02c82fl3SPR4ZLEN".
  Lemma mb_GZF : forall (i j cnt v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (An : Z) (ys : list word)
           (sg nc pc : Z) (xs : list word) (c0 c8 fl : word)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      XJA asegs R HIA h LB LF m dX spv lo 80
        (mm_frb c0 c8 (Z_to_bv 64 An) (Z_to_bv 64 (X + 10)) (Z_to_bv 64 (al_sb AL + Z.shiftr X 3)) (Z_to_bv 64 (al_sb AL + Z.shiftr (X + 10) 3)) (Z_to_bv 64 cnt)
                (Z_to_bv 64 (md_addr dB + 8)) fl (Z_to_bv 64 (md_addr dA + 8))) [(An, 4 * cnt)] v f hc LBc mc (mkMPD X sg nc pc xs padX LHeap) ->
      FBA asegs R LB LF dX lo LBc An cnt ys mc (mkMPD X sg nc pc xs padX LHeap) ->
      rideA R HIA LB LF m dX spv lo dA hc LBc mc (mkMPD X sg nc pc xs padX LHeap) ->
      rideA R HIA LB LF m dX spv lo dB hc LBc mc (mkMPD X sg nc pc xs padX LHeap) ->
      uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned spe) (bv_unsigned spv) d1 ->
      0 <= i <= md_n dA -> 0 <= j <= md_n dB -> i + j <= cnt ->
      v + AVOL_CALL + grow_PHI 1 <= mul_mid_PHI dA dB -> f + fr_charge d1 <= mul_mid_FR d1 -> cnt <= SZB ->
      aevtA asegs (KF asegs R HIA hc mo) POST
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned spv + -80)) gp tp xt0 xt1 xt2 spe (Z_to_bv 64 (bv_unsigned spv + -80))
                 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                 xs2 (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (al_sb AL + Z.shiftr (md_addr dB) 3)) (Z_to_bv 64 (- j)) (Z_to_bv 64 (md_addr dB))
                 (Z_to_bv 64 (md_addr dA)) xs8 (Z_to_bv 64 (al_sb AL + Z.shiftr (md_addr dA) 3)) (Z_to_bv 64 i) (Z_to_bv 64 X) xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x9f178) fc None mc (seg_rom asegs)).
  Proof.
    intros i j cnt v f hc LBc mc An ys sg nc pc xs c0 c8 fl xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 J FB RA RB UW HI HJ HN BV BF SZ.
    pose proof (JC c0 c8 (Z_to_bv 64 An) (Z_to_bv 64 (X + 10)) (Z_to_bv 64 (al_sb AL + Z.shiftr X 3)) (Z_to_bv 64 (al_sb AL + Z.shiftr (X + 10) 3)) (Z_to_bv 64 cnt) (Z_to_bv 64 (md_addr dB + 8)) fl (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 80 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in LEN1, NR1, SG1', CX1, OWN0, OWN1. unfold mpi_cells in CX1.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & PIN & PAL & PARR & P0 & PC & PIMG & OPm & P47). clear OWN0 OWN1.
    pose proof J as [MI0 ST0 FR0 HH0 HT0 HS0 HF0 HCS0 HV0 HFR0 MX0 AD0 PD0 NS0 OUT0 FRS0 FRA0 HPX0 OX0 XP0 XLS0 NM0]. cbn [app] in HH0.
    pose proof FB as [Ffr Ffr0 Fal Fnew Fnewc Fap Farr Flen Fcnt FXS Flo]. cbn [md_n] in Fcnt.
    pose proof (bv_unsigned_in_range 64 spv) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (SPR' : 0 <= bv_unsigned spv + -80 < 2^64) by lia.
    assert (PB : 0 < pc < 2^64) by lia.
    pose proof (hcs_ok asegs R HIA hc) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (art_alwf asegs R HIA) as ALWF'.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof FR0 as FR. pose proof ST0 as ST. unfold mm_frb in FR.
    replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) in FR, ST by (clear; lia).
    pose proof (hcs_stack asegs R HIA hc) as SCS0. pose proof (hm_top asegs R HIA hc _ LF mc HH0) as HTq.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned spv - lo))
      by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HT0 in HTq; clear - HTq TOP; lia]).
    cbn [md_addr] in OX0.
    lx_pre. lx_run_tac (PLAN [0xa7f14; 0x9f3b0] [] 20%N). lx_tree.
    all: try lxu_chk_leaves 0x9f3b0.
    all: try lx_same_mem.
    destruct (xga_zfree_pre _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ _ _ J FB eq_refl) as (ZIN & ZCH & ZLEN & ZB & ZN1).
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ZIN, ZCH, ZLEN, ZB.
    pose proof ZF as SPZ. unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ.
    eapply aevtA_call.
    { intros mo3 [HK3 MF3].
      eapply SPZ with (h := hc) (LB := (An, 4 * cnt) :: LBc) (LF := LF) (buf := pc) (len := 4 * nc) (lo := lo) (d := d1) (junk := u32s xs);
        rewrite ?(unsigned_lit (bv_unsigned spv + -80)) by exact SPR'; try eassumption; try reflexivity.
      all: try (right; split; [exact ZIN | rewrite <- ZLEN; exact ZCH]).
      all: try (rewrite HS0; eapply uwc_floor; [exact UW| lia]).
      all: try (rewrite HT0; lia).
      all: try (f_equal; lia).
      all: try (clear - SPA; Z.div_mod_to_equations; lia).
      all: unfold mul_mid_PHI, mul_mid_FR, grow_PHI, calls_FR, fr_charge in *; unfold AVOL_CALL in *; try lia. }
    clear SPZ.
    (intros ms' mo4' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)).
    destruct_exs PO. destruct PO as [E PO].
    pose proof (f_equal cfg_ms E) as E1. pose proof (f_equal cfg_model E) as E2. cbn [cfg_ms cfg_model] in E1, E2. clear E. subst ms' mo4'.
    rewrite ?(unsigned_lit (bv_unsigned spv + -80)) in PO by exact SPR'.
    ddestruct PO as (MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
    match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
    assert (HP4' : presA asegs R (lb_remove pc ((An, 4 * cnt) :: LBc)) LF (bv_unsigned spv - 80) (arl_stklo R) (hstkhi asegs R HIA hc) [(pc, pc + 4 * nc)] mc m4)
      by (replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) by lia; exact HP4).
    pose proof ST4 as ST4'. replace (bv_unsigned spv + -80) with (bv_unsigned spv - 80) in ST4' by lia.
    pose proof (xga_zfree_post _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ _ _ _ _ m4 h4 J FB eq_refl MI4 ST4' HP4' HT4 HS4 HF4 HCS4 HV4 HFR4 HH4) as D4.
    pose proof (rideA_zfree R HIA h LB LF m dX spv lo 80 _ JCc dA _ _ _ _ _ _ _ _ _ m4 h4 J FB RA eq_refl HP4' MI4 HCS4 HH4) as RA4.
    pose proof (rideA_zfree R HIA h LB LF m dX spv lo 80 _ JCc dB _ _ _ _ _ _ _ _ _ m4 h4 J FB RB eq_refl HP4' MI4 HCS4 HH4) as RB4.
    assert (UW4 : uwc asegs m4 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned spe) (bv_unsigned spv) d1).
    { rewrite <- HS0. eapply (uwc_presA_w R); [exact HP4'| rewrite HS0; exact UW| lia| | lia| apply hstkhi_le64; lia].
      intros a Ha. cbn [outside]. split; [lia| exact I]. }
    apply (aevtA_enter asegs (KF asegs R HIA h4 mo) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
    clear LAWS KINV CSOK SB64 SCS SCS0 HTq.
    pose proof D4 as [DMI DST4 DFR DHM DHT DHS DHF DHCS DHV DHFR DCX DSG DSUB DKEEP DGONE DNEW DAPART DARR DLEN4 DCNT DXS DPRES DFRESH DAL DOX DLO DNM].
    pose proof (hcs_ok asegs R HIA h4) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (AIh_laws asegs R HIA h4) as LAWS. pose proof (KF_kinv asegs R HIA h4 mo) as KINV.
    pose proof DFR as FR4. pose proof DST4 as ST4b. unfold mm_frb in FR4.
    replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) in FR4, ST4b by (clear; lia).
    pose proof (hcs_stack asegs R HIA h4) as SCS0. pose proof (hm_top asegs R HIA h4 _ LF m4 DHM) as HTq.
    assert (SCS : crange (hcs asegs R HIA h4) lo (bv_unsigned spv - lo))
      by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite DHT in HTq; clear - HTq TOP; lia]).
    lx_pre. lx_run_tac (PLAN [0x9f1a8; 0x9f3b0] [] 20%N). lx_tree.
    all: try lx_same_mem.
    all: try lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 0x9f1a8) _ _ _ _] => mb_apply (mb_GFIN i j cnt); mb_budget
         end.
    all: try eassumption.
    all: try (unfold mul_mid_SZ in *; lia).
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "01`0@L1000564579.185 L11478799281.267L11498238122.267L11498601372.151L11500765722.11 L11739978964.243L11870536053.283L11870765429.282L11870765813.183L1327100147.279 L1327100147.280 L1342025005.4   L14676623767.182L17973581596.280L17973581596.285L17979582360.285L20806295964.267L2139152316.197 L21767076675.184L22196713738.13 L22468532914.280L22468532914.285L22479317558.285L22481098759.267L22869344452.282L22881911409.267L22883373185.4  L23075838694.182L23183378982.287L23183427879.286L23494156239.230L24159491858.267L26056220419.260L26056220436.141L261133871.202  L2660365526.151 L2660663264.267 L26680472829.290L26830527540.185L28315228561.174L28315228561.221L29893873452.267L31509529227.281L31523938133.4  L32785674345.12 L34861500360.2  L35622389929.183L35622390185.148L35629037746.204L35653326272.192L3605837480.201 L3605837480.244 L38236168752.285L38237949953.267L38240603956.242L38250484404.280L40435166955.278L40435166955.279L40449602357.4  L40728356595.11 L40730369909.151L43877802600.280L43882045661.267L43884450540.285L43892363333.282L44080968951.146L45174768033.0  L46732241046.2  L46754236722.219L4760794149.200 L47845402596.151L49150858452.14 L50242520950.197L521871525.151  L54515112420.11 L5655253794.267 L57212878520.272L57628690626.279L57628699659.256L57983707768.267L58655890651.151L58656169564.287L58656251229.286L59310629840.151L60109463145.192L60111543915.285L60570960132.277L60570960132.278L60576273221.2  L61239750531.183L61564831532.151L62031034347.185L62037225709.288L62663396185.146L64562932110.3  L64569504848.282L64660463689.267L65446851286.199L65699767598.281L65714698480.3  L66151427842.16 L66547992416.290L66858459239.267L67104458864.151L68352032331.142L68367056493.143L7342806496.285 L7400112281.3   L7414521159.282 L917348036.256  L936947614.285  L994173029.288  00000`02?03[04Z04[05a06_07]08I08J08K08L0980:70;K0<_0>B0?70?c0?d0@[0AY0BW0CU0Dg0FE0FF0GD0HX0Il0K50LI0MK0N_0OZ0PP0QX0Rd0SP0T;0U90V?0WL0WM0WN0WV0XB0Xn0Y]0ZV0[U0]20^30_40`N0aE0bO0cY0cZ0c[0dV0eQ0fR0gS0hg0iS0iT0i\0k60l70m;0m<0mk0o<0o=10Y11m13914615J16617418218318f19k19l19m19n1:l1<;1=D1>i1?Y1?Z1A<1BU1CV1E81E91ET1GM1GN1HD1I71Ij1Ik1Il1Im1KF1M01N2S1R3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c322fl3SPRS1R3spv1X3xs02dA2dB2lo1i1j2nc2pc2xs2c02c83c163c322fl3LOS2X03SPR2An4Fcnt3An02N12P03H124SLEN4DLENS1R3spv1X3xs02dA2dB2lo4SLO21i1j2nc2pc2xs2c02c83c163c322fl2X03SPR4NRAM2An3An02N12P04SLEN4DLENS1R3spv1X3xs02dA2dB2lo4SLO21i1j3dXc2c02c83c163c322fl2X03SPR3NRMFS1R3spv1X3xs02dA2dB2d11i1j1f2nc2pc2xs2c02c83c163c322fl2BF2An4SLEN4DLENS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2An4SLEN4DLENS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2An4SLEN4DLENS1R3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c322flFFFS1R3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c322flS1R1X3xs02dA2dB1i1j2nc2xs2c02c83c163c322fl2An4Fcnt2N14SLEN4DLENS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2X03SPR2An4Fcnt3An02N12P04SLEN4DLENS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2X03SPR2An4Fcnt3An02N12P04SLEN4DLENS1R3spv1X3xs02dA2dB2lo1i1j2nc2pc2xs2c02c83c163c322fl3LOS2X03SPR2An4Fcnt3Flo3An02N12P03H124SLEN4DLENS1R3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c322fl2HN2HC2AnS1R3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c322flFS1R1X3xs02dA2dB1i1j2nc2xs2c02c83c163c322fl2An4SLEN4DLENS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2An4SLEN4DLENS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2An4SLEN4DLENS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2An4SLEN4DLENS1R3spv1X3xs02dA2dB2lo1i1j2nc2pc2xs2c02c83c163c322fl3LOS4ALO'4LEN12N12PC4SLEN4DLENS1R3spv1X3xs02dA2dB2lo1i1j2nc2pc2xs2c02c83c163c322fl3LOS4ALO'2X03SPR2An3An02N12P02PC4SLEN4DLENFS1R3spv1X3xs02dA2dB1i1j1v3dXc2c02c83c163c322fl2HI2HJ2BV2X03SPRS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2X03SPR2An4Fcnt3An02N12P04SLEN4DLENS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2X03SPR2An4Fcnt3An02N12P04SLEN4DLENS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2X03SPR2An3An02N12P03P47S1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2X03SPR2An4Fcnt3An02N12P04SLEN4DLENS1R3spv1X3xs02dA2dB1i1j2nc2xs2c02c83c163c322fl4SP644SPR'4SLEN4DLENS1R3spv1X3xs02dA2dB2lo4SLO21i1j3dXc2c02c83c163c322fl5NEEDR3LOS4SP644ALO'4ACP'2X03SPRS1R3spv1X3xs02dA2dB1i1j2c02c83c163c322fl2X03SPR2An4Flen3An0S1R3HIA1h3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c322fl3TOPS1R3HIA1h3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl3TOP2An4SLEN4DLENS1R3HIA1h3spv1X3xs02dA2dB2lo1i1j2nc2pc2xs2c02c83c163c322fl2An4SLEN4DLEN1y2HyS1R3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c322flS1R3spv1X3xs02dA2dB1i1j2c02c83c163c322fl2AnS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2An4SLEN4DLENS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl3XP02An4SLEN4DLEN3SEPS1R1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl4LEN13XP02An2N12P04SLEN4DLEN3SEPFFS3spv2loS1R3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c322flS1R3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c322flS1R3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c322fl2AnS1R3HIA1h3spv1X3xs02dA2dB2lo3XSC1i1j3dXc2c02c83c163c322flS1R3spv1X2nX3xs02dA2dB1i1j2c02c83c163c322fl2HI2HJ2X03SPR2An3An0S1R3spv1X2nX3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2HI2HJ2X03SPR2An4Fcnt3An02N12P04SLEN4DLENS1R3spv1X3xs02dA2dB2lo1i1j2nc2pc2xs2c02c83c163c322fl2An4SLEN4DLENS1R3spv1X3xs02dA2dB2lo1i1j2nc2pc2xs2c02c83c163c322fl2An4SLEN4DLENS1R3spv1X3xs02dA2dB1i1j1v2nc2pc2xs2c02c83c163c322fl2HI2HJ2BV2X03SPR2An3An02N12P04SLEN4DLENS1R1X3xs02dA2dB2lo1i1j2nc2xs2c02c83c163c322fl4SLEN4DLENS1R3spv1X3xs02dA2dB2lo1i1j2nc2xs2c02c83c163c322fl2An4Fcnt3Flo2N14SLEN4DLENS1R3spv1X3xs02dA2dB2lo1i1j2nc2xs2c02c83c163c322fl2An4Fcnt3Flo2N14SLEN4DLENFFS1R3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c322fl2HN2X04LEN13SPRS1R3spv1X3xs02dA2dB2lo1i1j2nc2xs2c02c83c163c322fl4SLEN4DLENS1R3spv1X3xs02dA2dB2lo1i1j2nc2pc2xs2c02c83c163c322fl2An4SLEN4DLENS1R3spv1X3xs02dA2dB2lo1i1j2nc2pc2xs2c02c83c163c322fl2An4SLEN4DLENS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2X04LEN13SPR2An3An02N12P04SLEN4DLENS1R3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c322flSS3spv2loS1R3spv1X3xs02dA2dB2lo4SLO21i1j3dXc2c02c83c163c322fl5NEEDR2X03X164LEN13SPR2An4Fcnt3Flo3An0S1R3spv1X3xs02dA2dB2d12D01i1j1f2c02c83c163c322fl2BF2X03SPR2An3An0S1R2LB3spv1X3xs02dA2dB4C24H1i1j3LBc3dXc2c02c83c163c322fl2X03SPR4C24cFS1R3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c322fl2AnS1R3HIA1h3spv1X3xs02dA2dB2d12D04BUDF1i1j1f2hc3dXc2c02c83c163c322fl2BF2X04HFR03SPRFS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2X03SPR2An4Fcnt3An02N12P04SLEN4DLEN3A473P47S1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2X03SPR2An4Fcnt3An02N12P04SLEN4DLENS1R3spv1X3xs02dA2dB2lo1i1j2nc2pc2xs2c02c83c163c322fl3XP02An4SLEN4DLEN3x292H2S1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl3XP02An1y2HyS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2X03SPR2An4Fcnt3An02N12P04SLEN4DLENS1R3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c322flS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2An4SLEN4DLENS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2An4SLEN4DLENFS1R3spv1X3xs02dA2dB2lo1i1j3dXc2c02c83c163c322fl3LOSS1R3spv1X3xs02dA2dB2lo1i1j2nc2pc2xs2c02c83c163c322fl3LOS2An4SLEN4DLENFFFS1R3spv1X3xs02dA2dB2d12D01i1j1f3dXc2c02c83c163c322fl2BF2X03SPRS1R3HIA1h3spv1X3xs02dA2dB3BUD1i1j1v2hc3dXc2c02c83c163c322fl2HI2HJ2BV2X03HV03SPRS1R3spv1X3xs02dA2dB2lo4SLO21i1j3dXc2c02c83c163c322fl5NEEDR3LOS2X03X163SPRS1R3spv1X3xs02dA2dB2lo4SLO21i1j2nc2pc2xs2c02c83c163c322fl5NEEDR3LOS2X03X163SPR2An3An02N12P04SLEN4DLENS1R3spv1X3xs02dA2dB3XSD1i1j3dXc2c02c83c163c322flFS1R3spv1X3xs02dA2dB2lo4SLO21i1j2nc2xs2c02c83c163c322fl5NEEDR3LOS4ALO'2An4Fcnt3Flo3AnC2N14SLEN4DLENS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl2X03SPR2An4Fcnt3An02N12P04SLEN4DLEN4LEN1S1R3spv1X3xs02dA2dB1i1j1v2c02c83c163c322fl2HI2HJ2BV2X03SPR2An3An0S1R3spv1X3xs02dA2dB2lo4SLO21i1j2nc2xs2c02c83c163c322fl5NEEDR3LOS4ALO'2An4Fcnt3Flo3AnC2N14SLEN4DLENFS3spv2r03SPA1q1r1H2H02q02H4S1R3HIA1h3spv1X3xs02dA2dB2lo4SLO21i1j2nc2pc2xs2c02c83c163c322fl5NEEDR3LOS2X03SPR2An4Fcnt3Flo3An02N12P03H124SLEN4DLEN1y2HyFS1R3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c322fl2HC2X03SPRS1R3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c322fl2X03SPRS1R3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c322fl2X03SPRFFFS1R3spv1X3xs02dA2dB2lo4SLO21i1j2pc2xs2c02c83c163c322fl5NEEDR3LOS2X03SPR2An3Flo3An02P03H12S1R3HIA1h3spv1X3xs02dA2dB2lo1i1j2hc2nc2pc2xs2c02c83c163c322fl3TOP2X03HT03SPR2h23HT22An3An02N12P04SLEN4DLENS1R3spv1X3xs02dA2dB1i1j2nc2pc2xs2c02c83c163c322fl3SPR2An4SLEN4DLEN".
  Lemma mb_GROW : forall (i j v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
           (c0 c8 c16 c32 fl : word)
           (xt0 xt1 xt2 xa2 xa5 xa7 xt3 xt4 xt5 xt6 : word),
      XJA asegs R HIA h LB LF m dX spv lo 80
        (mm_frb c0 c8 c16 (Z_to_bv 64 (X + 10)) c32 (Z_to_bv 64 (al_sb AL + Z.shiftr (X + 10) 3)) (Z_to_bv 64 (j + i))
                (Z_to_bv 64 (md_addr dB + 8)) fl (Z_to_bv 64 (md_addr dA + 8))) [] v f hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dA hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dB hc LBc mc dXc ->
      uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned spe) (bv_unsigned spv) d1 ->
      0 <= i <= md_n dA -> 0 <= j <= md_n dB -> md_n dXc < j + i -> j + i <= 10000 ->
      v <= 0 -> f <= 0 -> md_n dXc <= SZB ->
      aevtA asegs (KF asegs R HIA hc mo) POST
        (MS (mkR (Z_to_bv 64 0x9f124) (Z_to_bv 64 (bv_unsigned spv + -80)) gp tp xt0 xt1 xt2 spe (Z_to_bv 64 (bv_unsigned spv + -80))
                 (Z_to_bv 64 (j + i)) (Z_to_bv 64 4) xa2 (Z_to_bv 64 (X + 10)) (Z_to_bv 64 (al_sb AL + Z.shiftr (X + 10) 3)) xa5 (Z_to_bv 64 X) xa7
                 xs2 (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (al_sb AL + Z.shiftr (md_addr dB) 3)) (Z_to_bv 64 (- j)) (Z_to_bv 64 (md_addr dB))
                 (Z_to_bv 64 (md_addr dA)) xs8 (Z_to_bv 64 (al_sb AL + Z.shiftr (md_addr dA) 3)) (Z_to_bv 64 i) (Z_to_bv 64 (-16)) xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x69484) fc None mc (seg_rom asegs)).
  Proof.
    intros i j v f hc LBc mc dXc c0 c8 c16 c32 fl xt0 xt1 xt2 xa2 xa5 xa7 xt3 xt4 xt5 xt6 J RA RB UW HI HJ HN HC BV BF SZ.
    pose proof (JC c0 c8 c16 (Z_to_bv 64 (X + 10)) c32 (Z_to_bv 64 (al_sb AL + Z.shiftr (X + 10) 3)) (Z_to_bv 64 (j + i)) (Z_to_bv 64 (md_addr dB + 8)) fl (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 80 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J as [MI0 ST0 FR0 HH0 HT0 HS0 HF0 HCS0 HV0 HFR0 MX0 AD0 PD0 NS0 OUT0 FRS0 FRA0 HPX0 OX0 XP0 XLS0 NM0]. cbn [app] in HH0.
    pose proof (bv_unsigned_in_range 64 spv) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (SPR' : 0 <= bv_unsigned spv + -80 < 2^64) by lia.
    assert (NRM : arl_need_malloc R <= arl_need_rt R) by (unfold arl_need_rt; lia).
    assert (NRAM : arl_need_amem R <= arl_need_rt R) by (unfold arl_need_rt; lia).
    assert (AMX : AMAX = 268435456) by reflexivity.
    pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J) as C24c.
    assert (XSLc : rw_cells asegs mc (bv_unsigned spv + 40) [C8 (Z_to_bv 64 X)]).
    { eapply (presA_rw_cells asegs R); [exact HPX0| exact XSL| apply client_range_stack; lia| cbn; split; [lia| exact I]]. }
    pose proof ST0 as ST0'. replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) in ST0' by lia.
    replace (Z_to_bv 64 0x69484) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := hc) (LB := LBc) (LF := LF) (cnt := j + i) (sz := 4) (lo := lo) (d := d1);
        rewrite ?(unsigned_lit (bv_unsigned spv + -80)) by exact SPR'; try eassumption; try reflexivity.
      all: try (rewrite HS0; eapply uwc_floor; [exact UW| lia]).
      all: try (rewrite HT0; lia).
      all: try (clear - SPA; Z.div_mod_to_equations; lia).
      all: try (intros _; lia).
      all: try (rewrite AMX; lia).
      all: unfold mul_mid_PHI, mul_mid_FR, grow_PHI, calls_FR, fr_charge in *; unfold AVOL_CALL in *; try lia. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2 & mo2 & E & PO).
    pose proof (f_equal cfg_ms E) as E1. pose proof (f_equal cfg_model E) as E2. cbn [cfg_ms cfg_model] in E1, E2. clear E. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned spv + -80)) in PO by exact SPR'.
    ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    pose proof ST2 as ST2'. replace (bv_unsigned spv + -80) with (bv_unsigned spv - 80) in ST2' by lia.
    assert (HP2' : presA asegs R LBc LF (bv_unsigned spv - 80) (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m2)
      by (replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) by lia; exact HP2).
    assert (XSL2 : rw_cells asegs m2 (bv_unsigned spv + 40) [C8 (Z_to_bv 64 X)]).
    { eapply (presA_rw_cells asegs R); [exact HP2| exact XSLc| apply client_range_stack; lia| cbn; exact I]. }
    assert (UW2 : uwc asegs m2 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned spe) (bv_unsigned spv) d1).
    { rewrite <- HS0. eapply (uwc_presA_w R); [exact HP2'| rewrite HS0; exact UW| lia| intros a Ha; exact I| lia| apply hstkhi_le64; lia]. }
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (art_alwf asegs R HIA) as ALWF'.
    pose proof (hcs_stack asegs R HIA h2) as SCS2.
    assert (SCSX : crange (hcs asegs R HIA h2) lo (bv_unsigned spv + 48 - lo)) by (eapply crange_sub; [exact SCS2| lia| rewrite HS2, HS0; lia]).
    destruct CASES as [[Er HH2] | (An & Er & A16 & HFRA & HAS & HH2 & HNEW)]; match type of Er with ?vv = _ => subst vv end.
    - pose proof (xa_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ _ _ _ J MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2) as J2.
      lx_pre. lx_run_tac (PLAN [0x9f1d4; 0x9f3b0] [] 10%N). lx_tree.
      all: try lxu_chk_leaves 0x9f3b0.
      all: try lx_same_mem.
      all: repeat match goal with H : _ \/ _ |- _ => assert_fails (constr_eq H XSD); clear H end.
      all: try lazymatch goal with
           | |- context [MS _ _ (Z_to_bv 64 0x9f1d4) _ _ _ _] =>
               lazymatch type of J2 with XJA _ _ _ _ _ _ _ _ _ _ _ _ _ ?vv ?ff _ _ _ _ =>
                 assert (BK1 : vv <= mul_mid_PHI dA dB) by (unfold lset_FR, mul_mid_PHI, mul_mid_FR, grow_PHI, calls_FR, fr_charge, AVOL_CALL in *; lia);
                 assert (BK2 : ff <= mul_mid_FR d1 + fr_charge 0) by (unfold lset_FR, mul_mid_PHI, mul_mid_FR, grow_PHI, calls_FR, fr_charge, AVOL_CALL in *; lia) end;
               assert (BK0 : -16 = 0 \/ -16 = MBEDTLS_ERR_MPI_ALLOC_FAILED) by (right; reflexivity);
               let KCLu := fresh "KCLu" in pose proof KCL as KCLu; unfold KCLB_stmt in KCLu; mb_apply (KCLu _ _ h2 LBc m2 dXc (-16)); mb_budget
           end.
      all: try (unfold mul_mid_SZ in *; lia).
    - replace ((j + i) * 4) with (4 * (j + i)) in HFRA, HAS, HH2, HNEW, HV2 by lia.
      destruct (xa_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ _ _ _ An (j + i) J MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 A16 HFRA HNEW ltac:(lia)) as [J2 F2].
      pose proof (rideA_transport R HIA h LB LF m dX spv lo 80 _ JCc dA _ _ _ _ _ _ _ _ _ _ J RA HP2' MI2 HCS2 HH2 ltac:(intros b' Hb; right; exact Hb)) as RA2.
      pose proof (rideA_transport R HIA h LB LF m dX spv lo 80 _ JCc dB _ _ _ _ _ _ _ _ _ _ J RB HP2' MI2 HCS2 HH2 ltac:(intros b' Hb; right; exact Hb)) as RB2.
      pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J2) as (_ & _ & _ & _ & CX2 & _ & _).
      pose proof (xa_aobjX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J2) as OX2. cbn [md_addr] in OX2.
      pose proof (xa_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J2) as FR2. unfold mm_frb in FR2.
      replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) in FR2 by lia.
      pose proof F2 as [Ffr Ffr0 Fal Fnew Fnewc Fap Farr Flen Fcnt FXS Flo].
      dpose HFRA as (An0 & AnC & AnD & HAP).
      assert (AB : 0 < An < 2^64) by lia.
      destruct dXc as [X' sg nc pc xs pad' own].
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HN, SZ, LEN1, NR1, SG1', CX1, OWN0, OWN1, AD0, PD0, NS0, XP0, XLS0, CX2, Fcnt.
      subst X' pad'. unfold mpi_cells in CX2.
      destruct own; [ | | exfalso; exact (NS0 eq_refl)].
      + ddestruct (OWN0 eq_refl) as (EP & EN & EL). subst pc nc xs.
        lx_pre. lx_run_tac (PLAN [0x9f1a8; 0x9f1d4; 0x9f3b0] [] 30%N). lx_tree.
        all: try lxu_chk_leaves 0x9f3b0.
        all: try lx_same_mem.
        all: repeat match goal with H : _ \/ _ |- _ => assert_fails (constr_eq H XSD); clear H end.
        all: try lazymatch goal with
             | |- context [MS _ _ (Z_to_bv 64 0x9f1a8) _ _ _ _] =>
                 let D2 := fresh "D2" in
                 pose proof (xga_null _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ _ _ J2 F2 eq_refl) as D2;
                 lazymatch type of D2 with XDA _ _ _ _ _ _ _ _ _ _ _ _ ?vv ?ff _ _ _ _ _ _ _ =>
                   assert (BG1 : vv + grow_PHI 1 <= mul_mid_PHI dA dB) by (unfold lset_FR, mul_mid_PHI, mul_mid_FR, grow_PHI, calls_FR, fr_charge, AVOL_CALL in *; lia);
                   assert (BG2 : ff <= mul_mid_FR d1) by (unfold lset_FR, mul_mid_PHI, mul_mid_FR, grow_PHI, calls_FR, fr_charge, AVOL_CALL in *; lia) end;
                 assert (BG3 : j + i <= SZB) by (unfold mul_mid_SZ in *; lia);
                 mb_apply (mb_GFIN i j (j + i)); mb_budget
             end.
        all: try eassumption.
        all: try (unfold mul_mid_SZ in *; lia).
      + ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & PIN & PAL & PARR & P0 & PC & PIMG & OPm & P47).
        assert (PB : 0 < pc < 2^64) by lia.
        lx_pre. lx_run_tac (PLAN [0x67dbc; 0x9f1d4; 0x9f1a8; 0x9f3b0] [(0x9f160, DJoin)] 40%N). lx_tree.
        all: try lxu_chk_leaves 0x9f3b0.
        all: try (exfalso; lxu_lor_align_leaf).
        lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => rename mx into m2b end.
        match goal with H : munch _ m2 m2b |- _ => rename H into MUb0 end.
        match goal with H : wmono _ m2 m2b |- _ => rename H into WMb end.
        match goal with H : mem_inv _ m2b |- _ => rename H into MIb end.
        match goal with H : stk _ m2b lo _ |- _ => rename H into STb end.
        match goal with H : rw_cells _ m2b (bv_unsigned spv + -80) _ |- _ => rename H into FRb end.
        assert (MUb : munch [(bv_unsigned spv + -80, bv_unsigned spv)] m2 m2b)
          by (eapply munch_weaken; [| exact MUb0]; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy; cbn [outside] in Hy |- *; lia).
        pose proof (mb_frst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J2 MUb WMb MIb STb FRb) as J3.
        assert (F3 : FBA asegs R LB LF dX lo LBc An (j + i) (repeat (Z_to_bv 64 0) (Z.to_nat (j + i))) m2b (mkMPD X sg nc pc xs padX LHeap)).
        { eapply fba_munch; [exact F2| exact MUb| exact WMb|]. cbn [disjoint_from]. split; [lia| exact I]. }
        assert (RA3 : rideA R HIA LB LF m dX spv lo dA h2 LBc m2b (mkMPD X sg nc pc xs padX LHeap))
          by (eapply (mb_frride dA); [exact J2| exact RA2| exact MUb| exact WMb]).
        assert (RB3 : rideA R HIA LB LF m dX spv lo dB h2 LBc m2b (mkMPD X sg nc pc xs padX LHeap))
          by (eapply (mb_frride dB); [exact J2| exact RB2| exact MUb| exact WMb]).
        pose proof (mb_fruwc _ _ UW2 MUb) as UW3.
        destruct (xga_memcpy_pre _ _ _ _ _ _ _ _ _ _ _ _ (JC _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ J3 F3 eq_refl)
          as (SBY & SLEN & DST & DLEN & SEP & _ & _ & _ & _ & OA & OP' & _ & A47 & INA & INP).
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in SBY, SLEN, DST, DLEN, SEP, OA, OP', A47, INA, INP.
        pose proof (xa_aobjX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J3) as OX3. cbn [md_addr] in OX3.
        pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J3) as HH3. cbn [app] in HH3.
        rewrite firstn_length, repeat_length in DST, DLEN.
        replace (Init.Nat.min (Z.to_nat nc) (Z.to_nat (j + i))) with (Z.to_nat nc) in DST, DLEN by lia.
        apply (u8arr_of_rw_cells asegs) in DST.
        repeat match goal with H : munch _ _ m2b |- _ => clear H end.
        repeat match goal with H : _ \/ _ |- _ =>
          assert_fails (constr_eq H XSD); assert_fails (constr_eq H SEP); assert_fails (constr_eq H A47);
          assert_fails (constr_eq H P47); assert_fails (constr_eq H INA); assert_fails (constr_eq H INP); clear H end.
        pose proof (munch_refl [(An, An + 4 * nc); (lo, bv_unsigned spv + -80)] m2b) as MU. pose proof (wmono_refl asegs m2b) as WM.
        pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_MM) as SPC. unfold A_ASAN_MEMCPY_MM in SPC.
        acallxA_sp (bv_unsigned spv + -80)
          (eapply SPC with (h := h2) (LB := (An, 4 * (j + i)) :: LBc) (LF := LF) (DST := An) (SRC := pc) (n := 4 * nc) (lo := lo) (ss := u32s xs);
           rewrite ?(unsigned_lit (bv_unsigned spv + -80)) by exact SPR';
           try eassumption; try reflexivity;
           first [ left; rewrite AMC; reflexivity
                 | rewrite u32s_length, firstn_length, repeat_length; lia
                 | rewrite u32s_length; lia
                 | eapply aobj_sub; [exact OA| lia| lia]
                 | eapply crange_sub; [exact SCSX| lia| lia]
                 | eapply client_wrange_block; [apply in_or_app; left; left; reflexivity| lia| lia]
                 | rewrite HT2, HT0; lia
                 | f_equal; lia
                 | lia ]).
        clear SPC.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        match goal with H : u8arr asegs m3 An (u32s xs) |- _ => rename H into HPA end.
        match goal with H : stk asegs m3 lo _ |- _ => rename H into ST3 end.
        match goal with H : HM asegs R HIA h2 _ LF m3 |- _ => rename H into HH4 end.
        match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
        first [ match goal with H : aobj asegs AL (hcs asegs R HIA h2) m3 X 16 |- _ => rename H into OX4 end
              | match goal with H : aobj asegs AL (hcs asegs R HIA h2) m3 (md_addr dX) 16 |- _ => rename H into OX4 end ].
        pose proof ST3 as ST3'. replace (bv_unsigned spv + -80) with (bv_unsigned spv - 80) in ST3' by lia.
        apply (rw_cells_of_u8arr asegs) in HPA. rewrite u32s_length in HPA.
        replace (4 * length xs)%nat with (Z.to_nat (4 * nc)) in HPA by lia.
        pose proof MU as MU3'. replace (bv_unsigned spv + -80) with (bv_unsigned spv - 80) in MU3' by lia.
        destruct (xga_memcpy_post _ _ _ _ _ _ _ _ _ _ _ _ (JC _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ m3 J3 F3 eq_refl MU3' WM MI3 ST3' HPA HH4 OX4) as [J4 F4].
        assert (WC3 : w_client (hcs asegs R HIA h2) [(An, An + 4 * nc); (lo, bv_unsigned spv + -80)]).
        { unfold w_client; apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [eapply aobj_crange; exact OA| lia| lia]|].
          apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCSX| lia| lia]| apply Forall_nil]. }
        pose proof (rideA_fresh_munch R HIA h LB LF m dX spv lo 80 _ (JC _ _ _ _ _ _ _ _ _ _) dA _ _ _ _ _ _ _ _ _ (4 * nc) m3 (bv_unsigned spv + -80) J3 F3 RA3 ltac:(lia) ltac:(lia) MU WM WC3) as RA4.
        pose proof (rideA_fresh_munch R HIA h LB LF m dX spv lo 80 _ (JC _ _ _ _ _ _ _ _ _ _) dB _ _ _ _ _ _ _ _ _ (4 * nc) m3 (bv_unsigned spv + -80) J3 F3 RB3 ltac:(lia) ltac:(lia) MU WM WC3) as RB4.
        assert (UW4 : uwc asegs m3 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned spe) (bv_unsigned spv) d1).
        { eapply uwc_munch; [exact UW3| exact MU| lia| apply hstkhi_le64; lia|].
          let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy. cbn [outside]. split; [lia| split; [lia| exact I]]. }
        repeat match goal with H : _ \/ _ |- _ => assert_fails (constr_eq H XSD); clear H end.
        repeat match goal with H : context [m2b] |- _ => clear H end.
        repeat match goal with H : context [m2] |- _ => clear H end.
        repeat match goal with H : context [mc] |- _ => clear H end.
        lazymatch type of J4 with XJA _ _ _ _ _ _ _ _ _ _ _ _ _ ?vv ?ff _ _ _ _ =>
          assert (BG1 : vv + AVOL_CALL + grow_PHI 1 <= mul_mid_PHI dA dB) by (unfold lset_FR, mul_mid_PHI, mul_mid_FR, grow_PHI, calls_FR, fr_charge, AVOL_CALL in *; lia);
          assert (BG2 : ff + fr_charge d1 <= mul_mid_FR d1) by (unfold lset_FR, mul_mid_PHI, mul_mid_FR, grow_PHI, calls_FR, fr_charge, AVOL_CALL in *; lia) end.
        assert (BG3 : j + i <= SZB) by (unfold mul_mid_SZ in *; lia).
        mb_apply (mb_GZF i j (j + i)).
        all: try eassumption.
        all: mb_budget.
        all: try (unfold mul_mid_SZ in *; lia).
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00_0@L19282607564.124L19282607564.128L19282607691.121L19284704719.125L19843867808.146L21037814902.123L21429646844.146L22270718249.125L22270718638.122L22270718638.123L22274952941.141L27358724562.138L31608409925.125L31610506433.121L31610507078.124L31610507078.128L35629214198.1  L35668120833.7  L39735140427.127L49306746424.141L50185110358.129L50185204082.146L50187207509.126L50187207509.127L54179191577.141L54183339229.125L54183339866.122L54183339866.123L56958841328.141L57329670105.138L57628700040.160L59308579543.123L59310676307.127L59314873579.2  L59314873579.3  L60098763854.3  L6448495517.126 L6448495517.127 L6450592670.129 L6450661818.146 L6818944493.123 L6818944618.125 L6823094702.141 L734755999.121  L734756632.124  L734756632.128  L736853787.125  00000100200300401O01P03203303403503603o04004104204304804P05I06d06e06f06g06h06i06j06k06l08N09G0:>0:?0:@0:A0:B0:L0:M0:N0:O0:P0:Q0:R0:S0:T0:U0:V0:WFFFFS1R3spv1X3xs02dA2dB2lo2d12D04SLO21f3dXc2c02c83c163c243c323c403c482fl2BF5NEEDR3LOS4ALO'2X01HFS1R3spv1X3xs02dA2dB2lo3NRA3NRB4SLO21i1v3dXc2c02c83c163c243c323c403c482fl2HI2BV5NEEDR3LOS4ALO'2X01HFFFFS3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c243c323c403c482fl2H8FFFFS3spvS1R3HIA1h3spv2lo3TOP3HTqS3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c243c323c403c482fl2H4S1R3spv1X3xs02dA2dB2lo2d12D04SLO21f3dXc2c02c83c163c243c323c403c482fl2BF5NEEDR3LOS4ALO'2X01HFFFFFFFFS1R3spv1X3xs02dA2dB2lo4SLO21i1j1v3dXc2c02c83c163c243c323c403c482fl2HI2HJ2BV5NEEDR3LOS4ALO'2X01H2H4S3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c243c323c403c482fl2H4S3spv1X3xs02dA2dB3dXc2c02c83c163c243c323c403c482fl1x2HxFFFFS1R2lo3LOSFFFFFFFFFFF".
  Lemma mb_SUM : forall (i j v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
           (c0 c8 c16 c24 c32 c40 c48 fl : word)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs11 xt3 xt4 xt5 xt6 : word),
      XJA asegs R HIA h LB LF m dX spv lo 80
        (mm_frb c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dB + 8)) fl (Z_to_bv 64 (md_addr dA + 8))) [] v f hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dA hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dB hc LBc mc dXc ->
      uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned spe) (bv_unsigned spv) d1 ->
      0 <= i <= md_n dA -> 0 <= j <= md_n dB -> v <= 0 -> f <= 0 -> md_n dXc <= SZB ->
      aevtA asegs (KF asegs R HIA hc mo) POST
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned spv + -80)) gp tp xt0 xt1 xt2 spe (Z_to_bv 64 (bv_unsigned spv + -80))
                 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 X) xa7
                 xs2 (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (al_sb AL + Z.shiftr (md_addr dB) 3)) (Z_to_bv 64 (- j)) (Z_to_bv 64 (md_addr dB))
                 (Z_to_bv 64 (md_addr dA)) xs8 (Z_to_bv 64 (al_sb AL + Z.shiftr (md_addr dA) 3)) (Z_to_bv 64 i) xs11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x9f0d4) fc None mc (seg_rom asegs)).
  Proof.
    intros i j v f hc LBc mc dXc c0 c8 c16 c24 c32 c40 c48 fl xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs11 xt3 xt4 xt5 xt6 J RA RB UW HI HJ BV BF SZ.
    pose proof (JC c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dB + 8)) fl (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 80 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    unfold mpi_cells in CX1. cbn [md_addr md_pad] in CX1.
    pose proof (xa_aobjX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as OX1. cbn [md_addr] in OX1.
    mb_base hc J. mb_frame J. mb_scs hc J LOS TOP HH.
    lx_pre. lx_run_tac (PLAN [0x9f1d4; 0x9f1c0; 0x69484; 0x9f3b0] [(0x9f104, DJoin)] 80%N). lx_tree.
    all: try lxu_chk_leaves 0x9f3b0.
    all: try lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 0x9f1d4) _ _ _ _] => lx_same_mem; let KCLu := fresh "KCLu" in pose proof KCL as KCLu; unfold KCLB_stmt in KCLu; mb_apply (KCLu v f hc LBc mc dXc (-16)); mb_budget
         | |- context [MS _ _ (Z_to_bv 64 0x9f1c0) _ _ _ _] => lx_same_mem; mb_apply (mb_LSETP i j); mb_budget
         | |- context [MS _ _ (Z_to_bv 64 0x69484) _ _ _ _] => mb_frleaf J RA RB UW; mb_apply (mb_GROW i j)
         end.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0@L21039556869.136L22706556809.145L22706556809.149L22706556809.159L22706556809.168L30202110817.157L35485415948.136L35629214198.1  L35668120833.7  L40004405063.157L53899675211.139L60098763854.3  L66149356042.139L66151013920.91 00001902@03G04N05U06Y07`07e08=09A0:I0:S0<D0<PS3spv1X2sX2nX2pX3xs04padX4ownX2dA2dB1k1r2c02c83c163c243c323c403c483c642HkS3spv1X2sX2nX2pX3xs04padX4ownX2dA2dB2c02c83c163c243c323c403c483c641x2HxS3spv1X2sX2nX2pX3xs04padX4ownX2dA2dB2c02c83c163c243c323c403c483c641x2HxS3spv1X2sX2nX2pX3xs04padX4ownX2dA2dB2c02c83c163c243c323c403c483c641x2HxS3spv1X2sX2nX2pX3xs04padX4ownX2dA2dB2c02c83c163c243c323c403c483c641x2HxS3spv1X2sX2nX2pX3xs04padX4ownX2dA2dB1r2c02c83c163c243c323c403c483c64S3spv1X2sX2nX2pX3xs04padX4ownX2dA2dB1r2c02c83c163c243c323c403c483c642HRS3spvS1R3HIA1h3spv2lo3TOP3HTqS3spv1X2sX2nX2pX3xs04padX4ownX2dA2dB1r2c02c83c163c243c323c403c483c64S3spv1X2sX2nX2pX3xs04padX4ownX2dA2dB1k2c02c83c163c243c323c403c483c643NB1S1R2lo3LOSS1R3spv1X2sX2nX2pX3xs04padX4ownX2dA2dB2lo4SLO21k1r2c02c83c163c243c323c403c483c642HR5NEEDR3LOS4ALO'4ACP'2X02B03NB0S2dB1r2Hk2HR".
  Lemma mb_BLOOP : forall (k : nat) (r i v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
           (c0 c8 c16 c24 c32 c40 c48 c64 : word)
           (xra xt0 xt1 xt2 xa2 xa3 xa4 fl xa7 xs5 xs11 xt3 xt4 xt5 xt6 : word),
      r <= Z.of_nat k ->
      XJA asegs R HIA h LB LF m dX spv lo 80
        (mm_frb c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dB + 8)) c64 (Z_to_bv 64 (md_addr dA + 8))) [] v f hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dA hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dB hc LBc mc dXc ->
      uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned spe) (bv_unsigned spv) d1 ->
      0 <= i <= md_n dA -> 0 <= r <= md_n dB -> v <= 0 -> f <= 0 -> md_n dXc <= SZB ->
      aevtA asegs (KF asegs R HIA hc mo) POST
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned spv + -80)) gp tp xt0 xt1 xt2 spe (Z_to_bv 64 (bv_unsigned spv + -80))
                 (Z_to_bv 64 (- r)) (Z_to_bv 64 (4 * r + -4)) xa2 xa3 xa4 fl (Z_to_bv 64 X) xa7
                 xs2 (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (al_sb AL + Z.shiftr (md_addr dB) 3)) xs5 (Z_to_bv 64 (md_addr dB))
                 (Z_to_bv 64 (md_addr dA)) xs8 (Z_to_bv 64 (al_sb AL + Z.shiftr (md_addr dA) 3)) (Z_to_bv 64 i) xs11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x9f054) fc None mc (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros r i v f hc LBc mc dXc c0 c8 c16 c24 c32 c40 c48 c64 xra xt0 xt1 xt2 xa2 xa3 xa4 fl xa7 xs5 xs11 xt3 xt4 xt5 xt6 Hk J RA RB UW HI HR BV BF SZ.
    - assert (R0 : r = 0) by (cbn [Z.of_nat] in Hk; lia). subst r.
      pose proof (JC c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dB + 8)) c64 (Z_to_bv 64 (md_addr dA + 8))) as JCc.
      pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
      pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 80 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
      destruct (mb_view _ _ _ _ _ _ _ _ J RB NXB) as (CEB & OEB & SGB & B0 & B16 & BAL).
      mb_base hc J. mb_frame J. mb_scs hc J LOS TOP HH.
      lx_pre. lx_run_tac (PLAN [0x9f054; 0x9f0d4; 0x9f3b0] [] 40%N). lx_tree.
      all: try lazymatch goal with
           | |- context [MS _ _ (Z_to_bv 64 0x9f3b0) _ _ _ _] => lxu_chk_leaf 0x9f3b0
           | |- context [MS _ _ (Z_to_bv 64 0x9f0d4) _ _ _ _] => mb_frleaf J RA RB UW; lx_apply (mb_SUM i 0)
           end.
    - rewrite Nat2Z.inj_succ in Hk.
      pose proof (JC c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dB + 8)) c64 (Z_to_bv 64 (md_addr dA + 8))) as JCc.
      pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
      pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 80 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
      destruct (mb_view _ _ _ _ _ _ _ _ J RB NXB) as (CEB & OEB & SGB & B0 & B16 & BAL).
      mb_base hc J. mb_frame J. mb_scs hc J LOS TOP HH.
      destruct (Z_lt_le_dec 0 (md_n dB)) as [NB1|NB0].
      + destruct (mb_scanf _ _ _ _ _ _ _ _ J RB NXB ltac:(lia)) as (EBY & LENZ & EP0 & OEL & EPAL & EPB).
        lx_pre. lx_run_tac (PLAN [0x9f054; 0x9f0d4; 0x9f3b0] [(0x9f070, DSplit); (0x9f074, DSplit); (0x9f09c, DJoin)] 80%N). lx_tree.
        all: try lazymatch goal with
             | |- context [MS _ _ (Z_to_bv 64 0x9f3b0) _ _ _ _] => lxu_chk_leaf 0x9f3b0
             | |- context [MS _ _ (Z_to_bv 64 0x9f054) _ _ _ _] => lx_same_mem; lx_apply (IH (r - 1) i)
             | |- context [MS _ _ (Z_to_bv 64 0x9f0d4) _ _ _ _] => mb_frleaf J RA RB UW; lx_apply (mb_SUM i r)
             end.
      + assert (R0 : r = 0) by lia. subst r.
        lx_pre. lx_run_tac (PLAN [0x9f054; 0x9f0d4; 0x9f3b0] [] 40%N). lx_tree.
        all: try lazymatch goal with
             | |- context [MS _ _ (Z_to_bv 64 0x9f3b0) _ _ _ _] => lxu_chk_leaf 0x9f3b0
             | |- context [MS _ _ (Z_to_bv 64 0x9f0d4) _ _ _ _] => mb_frleaf J RA RB UW; lx_apply (mb_SUM i 0)
             end.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020@L20626620866.109L32123553562.10900000S014S1X2sX2nX2pX3xs04padX4ownX2dB2X02B0S1X2sX2nX2pX3xs04padX4ownX2dB3NRB".
  Lemma mb_BENTRY : forall (i v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
           (c0 c8 c16 c24 c32 c40 c48 c64 : word)
           (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 fl xa7 xs4 xs5 xs11 xt3 xt4 xt5 xt6 : word),
      XJA asegs R HIA h LB LF m dX spv lo 80
        (mm_frb c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dB + 8)) c64 (Z_to_bv 64 (md_addr dA + 8))) [] v f hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dA hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dB hc LBc mc dXc ->
      uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned spe) (bv_unsigned spv) d1 ->
      0 <= i <= md_n dA -> v <= 0 -> f <= 0 -> md_n dXc <= SZB ->
      aevtA asegs (KF asegs R HIA hc mo) POST
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned spv + -80)) gp tp xt0 xt1 xt2 spe (Z_to_bv 64 (bv_unsigned spv + -80))
                 (Z_to_bv 64 (md_addr dB + 10)) xa1 xa2 xa3 xa4 fl (Z_to_bv 64 X) xa7
                 xs2 (Z_to_bv 64 (al_sb AL)) xs4 xs5 (Z_to_bv 64 (md_addr dB))
                 (Z_to_bv 64 (md_addr dA)) xs8 (Z_to_bv 64 (al_sb AL + Z.shiftr (md_addr dA) 3)) (Z_to_bv 64 i) xs11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x9f020) fc None mc (seg_rom asegs)).
  Proof.
    intros i v f hc LBc mc dXc c0 c8 c16 c24 c32 c40 c48 c64 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 fl xa7 xs4 xs5 xs11 xt3 xt4 xt5 xt6 J RA RB UW HI BV BF SZ.
    pose proof (JC c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dB + 8)) c64 (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 80 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    destruct (mb_view _ _ _ _ _ _ _ _ J RB NXB) as (CEB & OEB & SGB & B0 & B16 & BAL).
    mb_base hc J.
    lx_pre. lx_run_tac (PLAN [0x9f054; 0x9f3b0] [(0x9f038, DJoin)] 60%N). lx_tree.
    all: try lx_same_mem.
    all: try lxu_chk_leaves 0x9f3b0.
    all: try lx_apply (mb_BLOOP (Z.to_nat (md_n dB)) (md_n dB) i).
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L19277745157.118L21039556867.118L29534714416.116L40004405063.134L66149356170.116L66151013920.89 00000R01601Y02802f032S1X2sX2nX2pX3xs04padX4ownX2dA1r2HRS1X2sX2nX2pX3xs04padX4ownX2dA1k1r2HkS1X2sX2nX2pX3xs04padX4ownX2dA1k3NA1S1X2sX2nX2pX3xs04padX4ownX2dA1rS1X2sX2nX2pX3xs04padX4ownX2dA1k1r2HR2X02A03NA0S2dA1r2Hk2HR".
  Lemma mb_ALOOP : forall (k : nat) (r v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
           (c0 c8 c16 c24 c32 c40 c48 c64 : word)
           (xra xt0 xt1 xt2 xa3 xa4 xa5 xa7 xs5 xs10 xs11 xt3 xt4 xt5 xt6 : word),
      r <= Z.of_nat k ->
      XJA asegs R HIA h LB LF m dX spv lo 80
        (mm_frb c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dB + 8)) c64 (Z_to_bv 64 (md_addr dA + 8))) [] v f hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dA hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dB hc LBc mc dXc ->
      uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned spe) (bv_unsigned spv) d1 ->
      0 <= r <= md_n dA -> v <= 0 -> f <= 0 -> md_n dXc <= SZB ->
      aevtA asegs (KF asegs R HIA hc mo) POST
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned spv + -80)) gp tp xt0 xt1 xt2 spe (Z_to_bv 64 (bv_unsigned spv + -80))
                 (Z_to_bv 64 (md_addr dB + 10)) (Z_to_bv 64 r) (Z_to_bv 64 (4 * r + -4)) xa3 xa4 xa5 (Z_to_bv 64 X) xa7
                 xs2 (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (md_addr dA + 10)) xs5 (Z_to_bv 64 (md_addr dB))
                 (Z_to_bv 64 (md_addr dA)) xs8 (Z_to_bv 64 (al_sb AL + Z.shiftr (md_addr dA) 3)) xs10 xs11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x9ef4c) fc None mc (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros r v f hc LBc mc dXc c0 c8 c16 c24 c32 c40 c48 c64 xra xt0 xt1 xt2 xa3 xa4 xa5 xa7 xs5 xs10 xs11 xt3 xt4 xt5 xt6 Hk J RA RB UW HR BV BF SZ.
    - assert (R0 : r = 0) by (cbn [Z.of_nat] in Hk; lia). subst r.
      pose proof (JC c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dB + 8)) c64 (Z_to_bv 64 (md_addr dA + 8))) as JCc.
      pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 80 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
      destruct (mb_view _ _ _ _ _ _ _ _ J RA NXA) as (CEA & OEA & SGA & A0 & A16 & AAL).
      mb_base hc J.
      lx_pre. lx_run_tac (PLAN [0x9ef4c; 0x9f020; 0x9f3b0] [] 40%N). lx_tree.
      all: try lx_same_mem.
      all: try lx_apply (mb_BENTRY 0).
    - rewrite Nat2Z.inj_succ in Hk.
      pose proof (JC c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dB + 8)) c64 (Z_to_bv 64 (md_addr dA + 8))) as JCc.
      pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 80 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
      destruct (mb_view _ _ _ _ _ _ _ _ J RA NXA) as (CEA & OEA & SGA & A0 & A16 & AAL).
      mb_base hc J.
      destruct (Z_lt_le_dec 0 (md_n dA)) as [NA1|NA0].
      + destruct (mb_scanf _ _ _ _ _ _ _ _ J RA NXA ltac:(lia)) as (EBY & LENZ & EP0 & OEL & EPAL & EPB).
        lx_pre. lx_run_tac (PLAN [0x9ef4c; 0x9f020; 0x9f3b0] [(0x9ef68, DSplit); (0x9ef6c, DSplit); (0x9ef94, DJoin)] 80%N). lx_tree.
        all: try lx_same_mem.
        all: try lazymatch goal with
             | |- context [MS _ _ (Z_to_bv 64 0x9f3b0) _ _ _ _] => lxu_chk_leaf 0x9f3b0
             | |- context [MS _ _ (Z_to_bv 64 0x9ef4c) _ _ _ _] => lx_apply (IH (r - 1))
             | |- context [MS _ _ (Z_to_bv 64 0x9f020) _ _ _ _] => lx_apply (mb_BENTRY r)
             end.
      + assert (R0 : r = 0) by lia. subst r.
        lx_pre. lx_run_tac (PLAN [0x9ef4c; 0x9f020; 0x9f3b0] [] 40%N). lx_tree.
        all: try lx_same_mem.
        all: try lx_apply (mb_BENTRY 0).
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020@L31810927153.108L62564706333.10800000Q014S1X2sX2nX2pX3xs04padX4ownX2dA3NRAS1X2sX2nX2pX3xs04padX4ownX2dA2X02A0".
  Lemma mw_MID_B : forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
           (c0 c8 c16 c24 c32 c40 c48 c64 : word)
           (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa7 xs5 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
      XJA asegs R HIA h LB LF m dX spv lo 80
        (mm_frb c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dB + 8)) c64 (Z_to_bv 64 (md_addr dA + 8))) [] v f hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dA hc LBc mc dXc ->
      rideA R HIA LB LF m dX spv lo dB hc LBc mc dXc ->
      uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned spe) (bv_unsigned spv) d1 ->
      v <= 0 -> f <= 0 -> md_n dXc <= SZB ->
      aevtA asegs (KF asegs R HIA hc mo) POST
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned spv + -80)) gp tp xt0 xt1 xt2 spe (Z_to_bv 64 (bv_unsigned spv + -80))
                 (Z_to_bv 64 (md_addr dB + 10)) xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 X) xa7
                 xs2 (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (md_addr dA + 10)) xs5 (Z_to_bv 64 (md_addr dB))
                 (Z_to_bv 64 (md_addr dA)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 A_MPI_MUL_MID) fc None mc (seg_rom asegs)).
  Proof.
    intros until xt6. intros J RA RB UW BV BF SZ.
    pose proof (JC c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dB + 8)) c64 (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 80 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    destruct (mb_view _ _ _ _ _ _ _ _ J RA NXA) as (CEA & OEA & SGA & A0 & A16 & AAL).
    mb_base hc J.
    unfold A_MPI_MUL_MID.
    lx_pre. lx_run_tac (PLAN [0x9ef4c; 0x9f3b0] [(0x9ef34, DJoin)] 60%N). lx_tree.
    all: try lx_same_mem.
    all: try lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 0x9f3b0) _ _ _ _] => lxu_chk_leaf 0x9f3b0
         | |- context [MS _ _ (Z_to_bv 64 0x9ef4c) _ _ _ _] => lx_apply (mb_ALOOP (Z.to_nat (md_n dA)) (md_n dA))
         end.
  Qed.
End WMB.
