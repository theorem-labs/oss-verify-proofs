From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState Frame Mem Cells Arr CellsX HeapIface MpiCoreAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_ecp_red.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_journey.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section K1.
  Variable segs : list Segment.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA segs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Variables (h : HST segs R HIA) (LB LF : list blk) (m : mem) (dX : mpd) (sp : word) (lo FS : Z) (FRAME : list cell).
  Local Notation SP := (bv_unsigned sp).
  Local Notation X := (md_addr dX).
  Hypothesis JC : JCA segs R HIA h LB LF m dX sp lo FS FRAME.

  #[using="JC"] Lemma xa_kob : forall (EX : list blk) (v f : Z) (hc : HST segs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
      (XL : Z) (m' : mem) (h' : HST segs R HIA) (xs' : list word),
    XJA segs R HIA h LB LF m dX sp lo FS FRAME EX v f hc LBc mc dXc ->
    md_own dXc = LHeap -> XL <= md_n dXc ->
    mem_inv segs m' -> stk segs m' lo (SP - FS) ->
    presW segs R HIA hc (EX ++ LBc) LF (SP - FS) (arl_stklo R) [(md_p dXc, md_p dXc + 4 * XL)] mc m' ->
    hcs segs R HIA h' = hcs segs R HIA hc -> htop segs R HIA h' = htop segs R HIA hc ->
    hstkhi segs R HIA h' = hstkhi segs R HIA hc -> hflag segs R HIA h' = hflag segs R HIA hc ->
    havol segs R HIA h' = havol segs R HIA hc -> hfr segs R HIA h' = hfr segs R HIA hc ->
    HM segs R HIA h' (EX ++ LBc) LF m' ->
    u32arr segs m' (md_p dXc) xs' -> length xs' = length (md_limbs dXc) ->
    XJA segs R HIA h LB LF m dX sp lo FS FRAME EX v f h' LBc m' (relimb dXc xs').
  Proof.
    pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts segs R HIA h LB LF m dX sp lo FS FRAME JC) as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros EX v f hc LBc mc dXc XL m' h' xs' J EO XLN MI' ST' PW HCS' HT' HS' HF' HV' HFR' HH' ARR' LEN'.
    pose proof (xa_facts segs R HIA h LB LF m dX sp lo FS FRAME JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1 & CX1 & OWN0 & OWN1).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
    ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47).
    destruct PW as [HP0 _].
    pose proof (hcs_ok segs R HIA hc) as CSOKc.
    assert (CRX : client_range L ((EX ++ LBc) ++ fdata LF) (SP - FS) X 16)
      by (eapply (xa_crX segs R HIA h LB LF m dX sp lo FS FRAME JC); [exact J| clear - FS16; lia]).
    assert (HP' : presA segs R (mpd_keep LB dX) LF SP (arl_stklo R) (hstkhi segs R HIA h) [(X, X + 16)] mc m').
    { assert (TAILP : presA segs R (mpd_keep LB dX) LF SP (arl_stklo R) (hstkhi segs R HIA h)
                        [(md_p dXc, md_p dXc + 4 * md_n dXc); (X, X + 16)] mc m').
      { rewrite <- HS1.
        eapply (presA_weaken segs R (EX ++ LBc) (mpd_keep LB dX) LF LF (SP - FS) SP (arl_stklo R) (arl_stklo R) (hstkhi segs R HIA hc) (hstkhi segs R HIA hc));
          [exact HP0| intros b Hb; apply in_or_app; right; exact (xa_keep_sub segs R HIA h LB LF m dX sp lo FS FRAME _ _ _ _ _ _ _ _ J Hb)
          | intros b Hb; exact Hb| clear - FS16; lia| clear; lia| clear; lia| ].
        intros x Hx. cbn [outside] in Hx |- *. split; [clear - Hx XLN; lia| exact I]. }
      destruct (FRA1 (md_p dXc, 4 * md_n dXc) ltac:(unfold mpd_blk; rewrite EO; left; reflexivity)) as [HbX|HFR].
      + assert (EOX : md_own dX = LHeap /\ md_p dX = md_p dXc /\ md_n dX = md_n dXc).
        { unfold mpd_blk in HbX. destruct (md_own dX); try (destruct HbX; fail). destruct HbX as [E|[]]. injection E as E1 E2. split; [reflexivity| split; [exact E1| clear - E2 NR NR1; lia]]. }
        ddestruct EOX as (EOd & EP & EN).
        pose proof MX as [(_ & _ & _ & _ & _ & OWd) _]. rewrite EOd in OWd. ddestruct OWd as (_ & XINd & _).
        eapply (presA_drop_freed segs R HIA h LB LF (mpd_keep LB dX) [(X, X + 16)] (md_p dXc) (4 * md_n dXc) m mc m');
          [exact HH| rewrite <- EP, <- EN; exact XINd| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS LOSP FS16; lia| exact TAILP].
        intros b xb Hb Hr. unfold mpd_keep in Hb. rewrite EOd in Hb. apply filter_In in Hb. destruct Hb as [Hb Hne].
        split; [exact Hb|]. intros E. rewrite E, <- EP, <- EN in Hne. unfold blk_eqb in Hne. cbn in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne.
      + eapply (presA_drop_fresh segs R HIA h (mpd_keep LB dX) LF [(X, X + 16)] (md_p dXc) (4 * md_n dXc) mc m' SP); [exact TAILP| exact HFR| clear - LOS LOSP FS16; lia]. }
    assert (CXc : rw_cells segs m' (md_addr dXc) (mpi_cells (md_p dXc) (Z_to_bv 64 (md_sg dXc)) (md_n dXc) (md_pad dXc))).
    { pose proof MX1 as [(CX & _) _].
      eapply (presA_rw_cells segs R); [exact HP0| exact CX| |].
      - unfold mpi_cells; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite AD1. exact CRX.
      - unfold mpi_cells; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite AD1.
        split; [| exact I]. destruct (XP1 EO) as [K|K]; [left; clear - K XLN; lia| right; clear - K XLN; lia]. }
    assert (MXc : mpd_at segs m' LBc (relimb dXc xs')).
    { eapply relimb_at; [exact MX1| exact EO| exact CXc| exact ARR'| rewrite LEN'; exact LEN1]. }
    unfold relimb in MXc |- *.
    constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try assumption.
    - eapply (presA_rw_cells segs R); [exact HP0| exact FR1| rewrite FSZ; apply client_range_stack; clear; lia|].
      rewrite FSZ. cbn [disjoint_from]. split; [right; clear - PC ALO LOS LOSP XLN; lia| exact I].
    - rewrite HT'; exact HT1.
    - rewrite HS'; exact HS1.
    - rewrite HF'; exact HF1.
    - intros x Hx. rewrite HCS'. apply HCS1. exact Hx.
    - rewrite HV'; exact HV1.
    - rewrite HFR'; exact HFR1.
    - eapply presA_trans; [exact HPX1| exact HP'].
    - rewrite HCS'.
      eapply (presA_aobj0 segs R); [exact CSOKc| exact HP0| exact OX1| intros x Hx; eapply hcs_below_top; exact Hx|].
      right. split; [exact CRX| clear - ALO LOS LOSP; lia].
  Qed.
End K1.
