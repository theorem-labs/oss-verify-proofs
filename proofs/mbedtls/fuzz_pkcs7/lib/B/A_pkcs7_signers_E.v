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
     A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt A_pkcs7_signers_A A_pkcs7_signers_B A_pkcs7_signers_C A_pkcs7_signers_D.
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


  Local Notation sjZ := (SGJ (zeros 80) (Z_to_bv 8 0) (zeros 7) (zeros 96)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG NS1 STKsi NRT CWP PPLO BIN CWS SGLO CRDA DALO SLOS SLOL SLO TOP SPA TPV LOS"] Lemma calloc_stepA_x : forall (fx FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p : Z) (sgc : list cell) (Lc : list blk) mc moc hc (RET : Z) (Q : config -> Prop)
      (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
    0 <= fx -> lo <= bv_unsigned sp - fx - STKs ->
    gvA_x fx FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc mc moc hc ->
    havol asegs R HIA h + PHIa + (2 * 200 + AVOL_CALL) <= AVOL_MAX -> hfr asegs R HIA h + FFRa + fr_charge (d + 1) <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    (forall a, bv_unsigned sp <= a < hstkhi asegs R HIA h -> outside W a) ->
    0 <= RET < 2^64 -> RET mod 2 = 0 ->
    (forall m1 mo1 h1 (y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
        gvA_x fx FB sp1 W (PHIa + (2 * 200 + AVOL_CALL)) (FFRa + fr_charge (d + 1)) w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc m1 mo1 h1 ->
        presA asegs R (Lc ++ LB) ((FB, 64) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m1 ->
        aevtA asegs (KF asegs R HIA h1 mo1) Q
          (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 sp1) gp tp y0 y1 y2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 0) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                   s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v y3 y4 y5 y6)
              F (Z_to_bv 64 RET) fc None m1 (seg_rom asegs))) ->
    (forall m1 mo1 h1 (N : Z) (y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
        gvA_x fx FB sp1 W (PHIa + (2 * 200 + AVOL_CALL)) (FFRa + fr_charge (d + 1)) w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc ((N, 200) :: Lc) m1 mo1 h1 ->
        rw_cells asegs m1 N (signer_cells 0 0 sjZ) -> N mod 16 = 0 -> 0 < N -> N + 200 <= alloc_ceiling ->
        fresh_apart R LB LF N 200 -> fresh_apart R (Lc ++ LB) ((FB, 64) :: LF) N 200 ->
        presA asegs R (Lc ++ LB) ((FB, 64) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m1 ->
        aevtA asegs (KF asegs R HIA h1 mo1) Q
          (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 sp1) gp tp y0 y1 y2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 N) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                   s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v y3 y4 y5 y6)
              F (Z_to_bv 64 RET) fc None m1 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc moc) Q
      (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 1) (Z_to_bv 64 200) a2 a3 a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
          F (Z_to_bv 64 (arl_calloc R)) fc None mc (seg_rom asegs)).
  Proof.
    intros until s11v. intros FX0 SLOx D BUD BUDF UW WST RETR RETE KN KY. unfold A_pkcs7_signers_A.STKs in SLOx. pose proof D as D0. gvA_open D. rt_facts.
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
      eapply (heapA_calloc asegs R HIA) with (h := hc) (LB := Lc ++ LB) (LF := (FB, 64) :: LF) (cnt := 1) (sz := 200) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HHc | exact HK1 | exact LOS | exact TPV | exact UW1 | reflexivity
              | lazymatch goal with
                | |- stk _ _ lo _ => exact STlo
                | |- mem_inv _ _ => exact MIc
                | |- lo <= sp1 - arl_need_malloc R => clear - SLO SP1 NS1 STKsi0 NRT FX0 SLOx; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP FX0; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- 0 <= 1 => clear - FX0; lia
                | |- 0 <= 200 => clear - FX0; lia
                | |- 1 * 200 < AMAX => unfold AMAX; clear - FX0; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD HVc; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDF HFRc; lia
                end
              | c24_lit   (* [comment removed for export] *)
              | match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms2 mo2x dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2' & mo2 & E2 & PO). injection E2 as Ems Emo. subst ms2' mo2x.
    unfold call_postA in PO. cbv beta in PO.
    ddestruct PO as (u0 & u1 & u2 & r & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & Ems2 & MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    subst ms2.
    rewrite ?(unsigned_lit sp1) in ST2 by exact SP1R. rewrite ?(unsigned_lit sp1) in HP2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETR| exact RETE]).
    rewrite ?Z.mul_1_l in HV2. rewrite ?Z.mul_1_l in CASES.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo2) _ _ _ (conj HK2 (mo_frame_refl mo2))).
    destruct CASES as [[Er HH2] | (N & Er & NAL & NFR & NSTK & HH2 & NZ)]; subst r.
    - eapply KN; [| exact HP2].
      eapply (gvA_call0_x R HIA) with (fx := fx) (STKsi := STKsi) (Lc := Lc) (LBq := Lc ++ LB) (Lc' := Lc) (mc := mc) (moc := moc) (hc := hc);
        first [ exact D0 | exact FX0 | exact SLOx | exact SLO | exact MI2 | exact ST2 | exact (mo_frame_trans _ _ _ MF1 MF2) | exact HP2 | exact HT2 | exact HS2 | exact HF2 | exact HK2 | exact HCS2
              | exact HV2 | exact HFR2 | exact HH2 | (intros b Hb; apply in_or_app; right; exact Hb) | eassumption | match goal with |- ?g => idtac "GC0N-LEFT:" g end ].
    - pose proof NFR as NF. ddestruct NF as (N0 & N1 & N2 & N3).
      eapply (KY m2 mo2 h2 N).
      + eapply (gvA_call0_x R HIA) with (fx := fx) (STKsi := STKsi) (Lc := Lc) (LBq := Lc ++ LB) (Lc' := (N, 200) :: Lc) (mc := mc) (moc := moc) (hc := hc);
          first [ exact D0 | exact FX0 | exact SLOx | exact SLO | exact MI2 | exact ST2 | exact (mo_frame_trans _ _ _ MF1 MF2) | exact HP2 | exact HT2 | exact HS2 | exact HF2 | exact HK2 | exact HCS2
                | exact HV2 | exact HFR2 | exact HH2 | (intros b Hb; apply in_or_app; right; exact Hb) | eassumption | match goal with |- ?g => idtac "GC0Y-LEFT:" g end ].
      + eapply rw_cells_reshape; [exact NZ| vm_compute; repeat split; reflexivity| vm_compute; reflexivity].
      + exact NAL.
      + exact N0.
      + exact N1.
      + split; [exact N0|]. split; [exact N1|]. split; [exact N2|]. intros B j Hb. apply N3. apply in_app_iff in Hb. apply in_app_iff.
        destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb| right; apply (fdata_cons_sub (B, j) [] FB 64 LF); exact Hb].
      + exact NFR.
      + exact HP2.
  Qed.
  #[using="IMG NS1 STKsi NRT CWP PPLO BIN CWS SGLO CRDA DALO SLOS SLOL SLO TOP SPA TPV LOS"] Lemma calloc_stepA : forall (FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p : Z) (sgc : list cell) (Lc : list blk) mc moc hc (RET : Z) (Q : config -> Prop)
      (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
    gvA FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc mc moc hc ->
    havol asegs R HIA h + PHIa + (2 * 200 + AVOL_CALL) <= AVOL_MAX -> hfr asegs R HIA h + FFRa + fr_charge (d + 1) <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    (forall a, bv_unsigned sp <= a < hstkhi asegs R HIA h -> outside W a) ->
    0 <= RET < 2^64 -> RET mod 2 = 0 ->
    (forall m1 mo1 h1 (y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
        gvA FB sp1 W (PHIa + (2 * 200 + AVOL_CALL)) (FFRa + fr_charge (d + 1)) w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc m1 mo1 h1 ->
        presA asegs R (Lc ++ LB) ((FB, 64) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m1 ->
        aevtA asegs (KF asegs R HIA h1 mo1) Q
          (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 sp1) gp tp y0 y1 y2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 0) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                   s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v y3 y4 y5 y6)
              F (Z_to_bv 64 RET) fc None m1 (seg_rom asegs))) ->
    (forall m1 mo1 h1 (N : Z) (y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
        gvA FB sp1 W (PHIa + (2 * 200 + AVOL_CALL)) (FFRa + fr_charge (d + 1)) w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc ((N, 200) :: Lc) m1 mo1 h1 ->
        rw_cells asegs m1 N (signer_cells 0 0 sjZ) -> N mod 16 = 0 -> 0 < N -> N + 200 <= alloc_ceiling ->
        fresh_apart R LB LF N 200 -> fresh_apart R (Lc ++ LB) ((FB, 64) :: LF) N 200 ->
        presA asegs R (Lc ++ LB) ((FB, 64) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m1 ->
        aevtA asegs (KF asegs R HIA h1 mo1) Q
          (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 sp1) gp tp y0 y1 y2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 N) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                   s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v y3 y4 y5 y6)
              F (Z_to_bv 64 RET) fc None m1 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc moc) Q
      (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 1) (Z_to_bv 64 200) a2 a3 a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
          F (Z_to_bv 64 (arl_calloc R)) fc None mc (seg_rom asegs)).
  Proof.
    intros until s11v. exact (calloc_stepA_x 0 FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc mc moc hc RET Q t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v (Z.le_refl 0) ltac:(clear - SLO; lia)).
  Qed.
  End Call.
End Walk.
