(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag
     A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt A_pkcs7_signers_A A_pkcs7_signers_B A_pkcs7_signers_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition A_WFREE : Z := 0x6947c.                (* [comment removed for export] *) (* [comment removed for export] *)

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis CALLOC : arl_calloc R = A_WCALLOC.
  Hypothesis FREE : arl_free R = A_WFREE.
  (* [comment removed for export] *)
  Hypothesis GETTAG : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_G.
  Variables (PHIsi : Z -> Z) (FFRsi : Z -> Z -> Z) (CNTsi : Z -> Z) (STKsi : Z).
  Hypothesis SIGNER : pkcs7_signer_stmtA asegs R HIA PHIsi FFRsi CNTsi STKsi A_PKCS7_SIGNER.
  Hypothesis PHIsi_mono : forall n n', 0 <= n <= n' -> 0 <= PHIsi n <= PHIsi n'.
  Hypothesis FFRsi_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRsi n d <= FFRsi n' d.
  Hypothesis CNTsi_mono : forall n n', 0 <= n <= n' -> 0 <= CNTsi n <= CNTsi n'.
  Hypothesis STKsi0 : 0 <= STKsi.
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  (* [comment removed for export] *)
  Local Notation STKs := (A_pkcs7_signers_A.STKs R STKsi).
  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP P END BUF SIG DALG lo slo d : Z) (bs : list byte) (dtg dpad : word) (dlen dq : Z) (sj : signer_junk).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 1)%nat.
  Hypothesis HPP : rw_cells asegs m PP [C8 (Z_to_bv 64 P)].
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis HBY : bytes_at asegs m BUF bs.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis B30 : n < 2^30.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis HSG : rw_cells asegs m SIG (signer_cells 0 0 sj).
  Hypothesis ALS : SIG mod 8 = 0.
  Hypothesis SG0 : 0 < SIG.
  Hypothesis CWS : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) SIG SIGNER_SIZE.
  Hypothesis SGLO : SIG + SIGNER_SIZE <= lo.
  Hypothesis DSB : SIG + SIGNER_SIZE <= BUF \/ BUF + n <= SIG.
  Hypothesis HDA : rw_cells asegs m DALG (buf_cells dtg dpad dlen dq).
  Hypothesis ALD : DALG mod 8 = 0.
  Hypothesis DA0 : 0 < DALG.
  Hypothesis CRDA : client_range L (LB ++ fdata LF) lo DALG 24.
  Hypothesis DALO : DALG + 24 <= lo.
  Hypothesis Q1 : BUF <= dq. Hypothesis Q2 : 0 <= dlen. Hypothesis Q3 : dq + dlen <= BUF + n.
  Hypothesis D1 : PP + 8 <= SIG \/ SIG + SIGNER_SIZE <= PP.
  Hypothesis D2 : PP + 8 <= DALG \/ DALG + 24 <= PP.
  Hypothesis D3 : DALG + 24 <= SIG \/ SIG + SIGNER_SIZE <= DALG.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKs.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis NDL : List.NoDup (map fst LB).
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_pkcs7_cinfo.A_UAR_GOT, A_fuzz_entry.A_UAR_GOT in UARG; unfold A_SMALLOC_0 in SM0; unfold A_pkcs7_signers_A.STKs in SLO; unfold SIGNER_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation FSH0 :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].


  Local Notation NB := (END - P).
  Local Notation POST := (pkcs7_getsigners_postA asegs R HIA (PHIs PHIsi CNTsi) (FFRs FFRsi CNTsi) (CNTs CNTsi) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP P END SIG DALG NB lo slo d dtg dpad dlen dq m mo0).
  Local Notation X0 := [(PP, PP + 8); (SIG, SIG + 200)].
  Local Notation gvA := (gvA R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP P END BUF SIG DALG lo slo bs dtg dpad dlen dq).
  Local Notation gvA_x := (gvA_x R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP P END BUF SIG DALG lo slo bs dtg dpad dlen dq).

  Ltac gvA_open D :=
    destruct D as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & PRES & SP1 & SP1M & F64 & FRSH & CFB
                   & FHD & G4 & FSH & SAVE & RSL & STb & STlo & PPc & Hpc & CSG & SZC & DAc & BYc & OPP & OSG & ODA & OBUF & MIc & SSc).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG NS1 STKsi CWP PPLO BIN CWS SGLO CRDA DALO SLOS SLOL SLO TOP LOS"] Lemma gvA_call0_x : forall (fx FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p : Z) (sgc : list cell) (Lc : list blk) mc moc hc (LBq Lc' : list blk) (dV dF : Z) m1 mo1 h1,
    0 <= fx -> lo <= bv_unsigned sp - fx - STKs ->
    gvA_x fx FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc mc moc hc ->
    (forall b, In b LB -> In b LBq) ->
    mem_inv asegs m1 -> stk asegs m1 lo sp1 -> mo_frame moc mo1 ->
    presA asegs R LBq ((FB, 64) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m1 ->
    htop asegs R HIA h1 = htop asegs R HIA hc -> hstkhi asegs R HIA h1 = hstkhi asegs R HIA hc -> hflag asegs R HIA h1 = hflag asegs R HIA hc ->
    HK asegs R HIA h1 mo1 -> (forall y, hcs asegs R HIA hc y -> hcs asegs R HIA h1 y) ->
    havol asegs R HIA h1 <= havol asegs R HIA hc + dV -> hfr asegs R HIA h1 <= hfr asegs R HIA hc + dF ->
    HM asegs R HIA h1 (Lc' ++ LB) ((FB, 64) :: LF) m1 ->
    gvA_x fx FB sp1 W (PHIa + dV) (FFRa + dF) w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc' m1 mo1 h1.
  Proof.
    intros until h1. intros FX0 SLOx D SUBL MI1 ST1 MF1 HP1 HT1 HS1 HF1 HK1 HCS1 HV1 HFR1 HH1. unfold A_pkcs7_signers_A.STKs in SLOx. gvA_open D. rt_facts.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT. rewrite HTc, HSc in HT.
    pose proof FRSH as FRSH'. ddestruct FRSH' as (F0 & F1 & F2 & F3).
    assert (SUBq : forall b, In b (LB ++ fdata LF) -> In b (LBq ++ fdata ((FB, 64) :: LF))).
    { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (SUBL b Hb)| right; apply (fdata_cons_sub b [] FB 64 LF); exact Hb]. }
    assert (CRo : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L (LBq ++ fdata ((FB, 64) :: LF)) sp1 a k).
    { intros a k Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0| exact SUBq]. }
    assert (INHq : In (FB, 24) (LBq ++ fdata ((FB, 64) :: LF))) by (apply in_or_app; right; cbn; left; reflexivity).
    assert (INDq : In (FB + 32, 64 - 40) (LBq ++ fdata ((FB, 64) :: LF))) by (apply in_or_app; right; cbn; right; left; reflexivity).
    assert (CSHD : forall c, FB <= c < FB + 64 -> cshd R LBq ((FB, 64) :: LF) (arl_stklo R) (hstkhi asegs R HIA hc) c).
    { intros c Hc. right; right; left. exists (FB, 64). split; [left; reflexivity| cbn; exact Hc]. }
    split; [exact HH1|]. split; [exact HK1|]. split; [eapply mo_frame_trans; [exact MFc| exact MF1]|].
    split; [rewrite HT1; exact HTc|]. split; [rewrite HS1; exact HSc|]. split; [rewrite HF1; exact HFc|].
    split; [intros y Hy; exact (HCS1 y (HCSc y Hy))|].
    split; [clear - HVc HV1; lia|]. split; [clear - HFRc HFR1; lia|].
    split.
    { eapply (presW_call asegs R HIA h LB LF _ _ W m mc m1); [exact PRES| exact HP1| exact SUBL| intros b Hb; right; exact Hb
        | clear - SP1 FX0; lia| clear - LOS SLO NS1 STKsi0 NRT SLOx; lia| rewrite HSc; clear - FX0; lia| intros y Hy; exact I]. }
    split; [exact SP1|]. split; [exact SP1M|]. split; [exact F64|]. split; [exact FRSH|]. split; [exact CFB|].
    split; [eapply (presA_rw_cells asegs R); [exact HP1| exact FHD| cbn [cells_size csize Nat.add length]; eapply client_range_block; [exact INHq| clear - FX0; lia| clear - FX0; lia]| exact I]|].
    split; [eapply (presA_rw_cells asegs R); [exact HP1| exact G4| cbn [cells_size csize Nat.add length]; eapply client_range_block; [exact INDq| clear - FX0; lia| clear - FX0; lia]| exact I]|].
    split.
    { eapply (presA_shadow_cells_sh asegs R CS); [exact CSOK| cbn [cells_size csize Nat.add length]; exact CFB| clear - F64; Z.div_mod_to_equations; lia| clear - F0; lia| exact HP1| exact FSH|].
      cbn [cells_size csize Nat.add length]. intros c Hc. apply CSHD. clear - Hc. lia. }
    split; [eapply (presA_rw_cells asegs R); [exact HP1| exact SAVE| apply client_range_stack; clear - SP1 FX0; lia| exact I]|].
    split; [eapply (presA_rw_cells asegs R); [exact HP1| exact RSL| apply client_range_stack; clear - FX0; lia| exact I]|].
    split; [eapply (presA_stk asegs R); [exact HP1| exact STb| clear - FX0; lia| exact I]|].
    split; [exact ST1|].
    split; [eapply (presA_rw_cells asegs R); [exact HP1| exact PPc| cbn [cells_size csize Nat.add length]; apply CRo; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| exact I]|].
    split; [exact Hpc|].
    split; [eapply (presA_rw_cells asegs R); [exact HP1| exact CSG| rewrite SZC; apply CRo; [exact SGLO| exact (client_range_of_w L _ _ _ _ _ CWS)]| exact I]|].
    split; [exact SZC|].
    split; [eapply (presA_rw_cells asegs R); [exact HP1| exact DAc| cbn [cells_size csize Nat.add length buf_cells]; apply CRo; [exact DALO| exact CRDA]| exact I]|].
    split.
    { eapply (presA_bytes_at0 asegs R); [exact HP1| exact BYc|]. destruct (Nat.eq_dec (length bs) 0) as [E|NE]; [left; exact E| right].
      split; [| exact I]. eapply client_range_block; [apply in_or_app; left; exact (SUBL _ BIN)| clear - FX0; lia| clear - FX0; lia]. }
    split; [eapply (presA_aobj0 asegs R CS); [exact CSOK| exact HP1| exact OPP| intros y Hy; rewrite HSc; eapply hcs_below_top; exact Hy| right; split; [apply CRo; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| clear - LOS SLO SP1 NS1 STKsi0 NRT FX0 SLOx; lia]]|].
    split; [eapply (presA_aobj0 asegs R CS); [exact CSOK| exact HP1| exact OSG| intros y Hy; rewrite HSc; eapply hcs_below_top; exact Hy| right; split; [apply CRo; [exact SGLO| exact (client_range_of_w L _ _ _ _ _ CWS)]| clear - LOS SLO SP1 NS1 STKsi0 NRT FX0 SLOx; lia]]|].
    split; [eapply (presA_aobj0 asegs R CS); [exact CSOK| exact HP1| exact ODA| intros y Hy; rewrite HSc; eapply hcs_below_top; exact Hy| right; split; [apply CRo; [exact DALO| exact CRDA]| clear - LOS SLO SP1 NS1 STKsi0 NRT FX0 SLOx; lia]]|].
    split.
    { eapply (presA_aobj0 asegs R CS); [exact CSOK| exact HP1| exact OBUF| intros y Hy; rewrite HSc; eapply hcs_below_top; exact Hy|].
      destruct (Z.eq_dec n 0) as [E0|NE]; [left; rewrite E0; clear - FX0; lia| right]. split; [| clear - LOS SLO SP1 NS1 STKsi0 NRT FX0 SLOx; lia].
      eapply client_range_block; [apply in_or_app; left; exact (SUBL _ BIN)| clear - FX0; lia| clear - FX0; lia]. }
    split; [exact MI1|].
    eapply (presA_sshad asegs R); [exact HP1| exact SSc| exact SLOS| rewrite HSc; clear - HT TOP; lia].
  Qed.
  #[using="IMG NS1 STKsi CWP PPLO BIN CWS SGLO CRDA DALO SLOS SLOL SLO TOP LOS"] Lemma gvA_call0 : forall (FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p : Z) (sgc : list cell) (Lc : list blk) mc moc hc (LBq Lc' : list blk) (dV dF : Z) m1 mo1 h1,
    gvA FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc mc moc hc ->
    (forall b, In b LB -> In b LBq) ->
    mem_inv asegs m1 -> stk asegs m1 lo sp1 -> mo_frame moc mo1 ->
    presA asegs R LBq ((FB, 64) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m1 ->
    htop asegs R HIA h1 = htop asegs R HIA hc -> hstkhi asegs R HIA h1 = hstkhi asegs R HIA hc -> hflag asegs R HIA h1 = hflag asegs R HIA hc ->
    HK asegs R HIA h1 mo1 -> (forall y, hcs asegs R HIA hc y -> hcs asegs R HIA h1 y) ->
    havol asegs R HIA h1 <= havol asegs R HIA hc + dV -> hfr asegs R HIA h1 <= hfr asegs R HIA hc + dF ->
    HM asegs R HIA h1 (Lc' ++ LB) ((FB, 64) :: LF) m1 ->
    gvA FB sp1 W (PHIa + dV) (FFRa + dF) w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc' m1 mo1 h1.
  Proof.
    intros until h1. exact (gvA_call0_x 0 FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc mc moc hc LBq Lc' dV dF m1 mo1 h1 (Z.le_refl 0) ltac:(clear - SLO; lia)).
  Qed.

  (* [comment removed for export] *)
  #[using="IMG NS1 STKsi CWP PPLO BIN CWS SGLO CRDA DALO SLOS SLOL SLO TOP LOS"] Lemma gvA_free_x : forall (fx FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p : Z) (sgc : list cell) (Lc : list blk) mc moc hc (x : Z) m1 mo1 h1,
    0 <= fx -> lo <= bv_unsigned sp - fx - STKs ->
    gvA_x fx FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc mc moc hc ->
    In x (map fst Lc) ->
    mem_inv asegs m1 -> stk asegs m1 lo sp1 -> mo_frame moc mo1 ->
    presA asegs R (lb_remove x (Lc ++ LB)) ((FB, 64) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m1 ->
    htop asegs R HIA h1 = htop asegs R HIA hc -> hstkhi asegs R HIA h1 = hstkhi asegs R HIA hc -> hflag asegs R HIA h1 = hflag asegs R HIA hc ->
    HK asegs R HIA h1 mo1 -> (forall y, hcs asegs R HIA hc y -> hcs asegs R HIA h1 y) ->
    havol asegs R HIA h1 <= havol asegs R HIA hc + AVOL_CALL -> hfr asegs R HIA h1 <= hfr asegs R HIA hc + fr_charge (d + 1) ->
    HM asegs R HIA h1 (lb_remove x (Lc ++ LB)) ((FB, 64) :: LF) m1 ->
    gvA_x fx FB sp1 W (PHIa + AVOL_CALL) (FFRa + fr_charge (d + 1)) w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc (lb_remove x Lc) m1 mo1 h1.
  Proof.
    intros until h1. intros FX0 SLOx D HIN MI1 ST1 MF1 HP1 HT1 HS1 HF1 HK1 HCS1 HV1 HFR1 HH1. unfold A_pkcs7_signers_A.STKs in SLOx.
    rewrite (lb_remove_app_l x Lc LB HIN) in HP1, HH1.
    eapply (gvA_call0_x fx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Lc mc moc hc (lb_remove x Lc ++ LB) (lb_remove x Lc));
      [exact FX0| exact SLOx| exact D| intros b Hb; apply in_or_app; right; exact Hb| exact MI1| exact ST1| exact MF1| exact HP1| exact HT1| exact HS1| exact HF1| exact HK1| exact HCS1| exact HV1| exact HFR1| exact HH1].
  Qed.
  #[using="IMG NS1 STKsi CWP PPLO BIN CWS SGLO CRDA DALO SLOS SLOL SLO TOP LOS"] Lemma gvA_free : forall (FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p : Z) (sgc : list cell) (Lc : list blk) mc moc hc (x : Z) m1 mo1 h1,
    gvA FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc mc moc hc ->
    In x (map fst Lc) ->
    mem_inv asegs m1 -> stk asegs m1 lo sp1 -> mo_frame moc mo1 ->
    presA asegs R (lb_remove x (Lc ++ LB)) ((FB, 64) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m1 ->
    htop asegs R HIA h1 = htop asegs R HIA hc -> hstkhi asegs R HIA h1 = hstkhi asegs R HIA hc -> hflag asegs R HIA h1 = hflag asegs R HIA hc ->
    HK asegs R HIA h1 mo1 -> (forall y, hcs asegs R HIA hc y -> hcs asegs R HIA h1 y) ->
    havol asegs R HIA h1 <= havol asegs R HIA hc + AVOL_CALL -> hfr asegs R HIA h1 <= hfr asegs R HIA hc + fr_charge (d + 1) ->
    HM asegs R HIA h1 (lb_remove x (Lc ++ LB)) ((FB, 64) :: LF) m1 ->
    gvA FB sp1 W (PHIa + AVOL_CALL) (FFRa + fr_charge (d + 1)) w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc (lb_remove x Lc) m1 mo1 h1.
  Proof.
    intros until h1. exact (gvA_free_x 0 FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc mc moc hc x m1 mo1 h1 (Z.le_refl 0) ltac:(clear - SLO; lia)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG NS1 STKsi NRT CWP PPLO BIN CWS SGLO CRDA DALO SLOS SLOL SLO TOP SPA TPV LOS"] Lemma free_stepA_x : forall (fx FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p : Z) (sgc : list cell) (Lc : list blk) mc moc hc (x k : Z) (RET : Z) (Q : config -> Prop)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
    0 <= fx -> lo <= bv_unsigned sp - fx - STKs ->
    gvA_x fx FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc mc moc hc ->
    In (x, k) Lc -> List.NoDup (map fst (Lc ++ LB)) ->
    havol asegs R HIA h + PHIa + AVOL_CALL <= AVOL_MAX -> hfr asegs R HIA h + FFRa + fr_charge (d + 1) <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    (forall a, bv_unsigned sp <= a < hstkhi asegs R HIA h -> outside W a) ->
    0 <= RET < 2^64 -> RET mod 2 = 0 ->
    (forall m1 mo1 h1 (y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
        gvA_x fx FB sp1 W (PHIa + AVOL_CALL) (FFRa + fr_charge (d + 1)) w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc (lb_remove x Lc) m1 mo1 h1 ->
        presA asegs R (lb_remove x (Lc ++ LB)) ((FB, 64) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m1 ->
        aevtA asegs (KF asegs R HIA h1 mo1) Q
          (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 sp1) gp tp y0 y1 y2 sp (Z_to_bv 64 sp1) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                   s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v y3 y4 y5 y6)
              F (Z_to_bv 64 RET) fc None m1 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc moc) Q
      (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
          F (Z_to_bv 64 (arl_free R)) fc None mc (seg_rom asegs)).
  Proof.
    intros until s11v. intros FX0 SLOx D HIN ND BUD BUDF UW WST RETR RETE K. unfold A_pkcs7_signers_A.STKs in SLOx. pose proof D as D0. gvA_open D. rt_facts.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT. rewrite HTc, HSc in HT.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 STKsi0 NRT FX0 SLOx; lia).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0'.
    assert (UW1 : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA hc) (bv_unsigned sp) sp1 (d + 1)).
    { rewrite HSc.
      assert (UWa : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
      { eapply (uwc_presA R); [exact (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES)| exact UW| clear - FX0; lia| exact WST| clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO SPR NS1 STKsi0 NRT SLOx; lia]. }
      pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear - FX0; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UWa| clear - SP1 FX0; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0']. }
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_free asegs R HIA) with (h := hc) (LB := Lc ++ LB) (LF := (FB, 64) :: LF) (A := x) (n := k) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HHc | exact HK1 | exact LOS | exact TPV | exact UW1 | reflexivity
              | lazymatch goal with
                | |- In (x, k) (Lc ++ LB) => apply in_or_app; left; exact HIN
                | |- stk _ _ lo _ => exact STlo
                | |- mem_inv _ _ => exact MIc
                | |- lo <= sp1 - arl_need_free R => clear - SLO SP1 NS1 STKsi0 NRT FX0 SLOx; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP FX0; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD HVc; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDF HFRc; lia
                end
              | match goal with |- ?g => idtac "FREE-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms2 mo2x dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2' & mo2 & E2 & PO). injection E2 as Ems Emo. subst ms2' mo2x.
    unfold call_postA in PO. cbv beta in PO.
    ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & Ems2 & MI2 & ST2 & MF2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2).
    subst ms2.
    rewrite ?(unsigned_lit sp1) in ST2 by exact SP1R. rewrite ?(unsigned_lit sp1) in HP2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETR| exact RETE]).
    pose proof (gvA_free_x fx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x m2 mo2 h2 FX0 SLOx D0 ltac:(apply (in_map fst) in HIN; exact HIN) MI2 ST2 (mo_frame_trans _ _ _ MF1 MF2) HP2 HT2 HS2 HF2 HK2 HCS2 HV2 HFR2 HH2) as G2.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo2) _ _ _ (conj HK2 (mo_frame_refl mo2))).
    eapply K; [exact G2| exact HP2].
  Qed.
  #[using="IMG NS1 STKsi NRT CWP PPLO BIN CWS SGLO CRDA DALO SLOS SLOL SLO TOP SPA TPV LOS"] Lemma free_stepA : forall (FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p : Z) (sgc : list cell) (Lc : list blk) mc moc hc (x k : Z) (RET : Z) (Q : config -> Prop)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
    gvA FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc mc moc hc ->
    In (x, k) Lc -> List.NoDup (map fst (Lc ++ LB)) ->
    havol asegs R HIA h + PHIa + AVOL_CALL <= AVOL_MAX -> hfr asegs R HIA h + FFRa + fr_charge (d + 1) <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    (forall a, bv_unsigned sp <= a < hstkhi asegs R HIA h -> outside W a) ->
    0 <= RET < 2^64 -> RET mod 2 = 0 ->
    (forall m1 mo1 h1 (y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
        gvA FB sp1 W (PHIa + AVOL_CALL) (FFRa + fr_charge (d + 1)) w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc (lb_remove x Lc) m1 mo1 h1 ->
        presA asegs R (lb_remove x (Lc ++ LB)) ((FB, 64) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m1 ->
        aevtA asegs (KF asegs R HIA h1 mo1) Q
          (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 sp1) gp tp y0 y1 y2 sp (Z_to_bv 64 sp1) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                   s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v y3 y4 y5 y6)
              F (Z_to_bv 64 RET) fc None m1 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc moc) Q
      (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
          F (Z_to_bv 64 (arl_free R)) fc None mc (seg_rom asegs)).
  Proof.
    intros until s11v. exact (free_stepA_x 0 FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc mc moc hc x k RET Q t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v (Z.le_refl 0) ltac:(clear - SLO; lia)).
  Qed.
  End Call.
End Walk.
