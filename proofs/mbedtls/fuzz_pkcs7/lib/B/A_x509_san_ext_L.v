(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_crt_parse_stmts A_pkcs7_cinfo A_pkcs7_parse_A A_asn1_get_len A_asn1_free_named_data_list_shallow A_asn1_sequence_free A_x509_get_name_stmt A_x509_parse_san_A A_x509_seq_stmts A_x509_seq_stmtsE.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_x509_get_name_A.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_san_ext_A A_x509_san_ext_bud A_x509_san_ext_B A_x509_san_ext_C A_x509_san_ext_D A_x509_san_ext_E A_x509_san_ext_F A_x509_san_ext_G A_x509_san_ext_H A_x509_san_ext_I A_x509_san_ext_J A_x509_san_ext_K.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2S.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NA1 : 0 <= arl_need_amem R.
  Hypothesis AMS : arl_amemset R = 0x68258.
  Hypothesis AMC : arl_amemcpy R = 0x67dbc.
  Hypothesis CALLOC : arl_calloc R = A_WCALLOC.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  (* [comment removed for export] *)
  Variables (PHIp : Z -> Z) (FFRp : Z -> Z -> Z) (CNTp : Z -> Z) (STKp : Z).
  Hypothesis STKp0 : 0 <= STKp.
  Hypothesis PSAN : x509_parse_san_stmtA asegs R HIA PHIp FFRp CNTp STKp (LFMAX_CRT + 6) A_X509_PARSE_SAN.
  Hypothesis FREEL : asn1_free_named_data_list_shallow_stmtA asegs R HIA A_ASN1_FREE_NAMED_DATA_LIST_SHALLOW.
  Hypothesis SEQFREE : asn1_sequence_free_stmtA asegs R HIA A_ASN1_SEQUENCE_FREE.
  (* [comment removed for export] *)
  Hypothesis PHIp_mono : forall n n', 0 <= n <= n' -> 0 <= PHIp n <= PHIp n'.
  Hypothesis FFRp_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRp n d <= FFRp n' d.
  Hypothesis CNTp_mono : forall n n', 0 <= n <= n' -> 0 <= CNTp n <= CNTp n'.
  Hypothesis PHIp_add : forall a b, 0 <= a -> 0 <= b -> PHIp a + PHIp b <= PHIp (a + b).
  Hypothesis FFRp_add : forall a b d, 0 <= a -> 0 <= b -> FFRp a d + FFRp b d <= FFRp (a + b) d.
  Hypothesis CNTp_add : forall a b, 0 <= a -> 0 <= b -> CNTp a + CNTp b <= CNTp (a + b).
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R /\ arl_need_amem R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.

  (* [comment removed for export] *)
  Local Notation STKx := (A_x509_san_ext_A.STKx R STKp).
  Local Notation CNTx := A_x509_san_ext_bud.CNTx.
  Local Notation PHIx := (A_x509_san_ext_bud.PHIx PHIp CNTp).
  Local Notation FFRx := (A_x509_san_ext_bud.FFRx FFRp CNTp).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP CUR P END BUF lo slo d : Z) (bs : list byte) (ct cpad : word).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 5)%nat.
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
  Hypothesis HCUR : rw_cells asegs m CUR (seq_cells ct cpad 0 0 0).
  Hypothesis ALC : CUR mod 8 = 0.
  Hypothesis CUR0 : 0 < CUR.
  Hypothesis CWC : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CUR 32.
  Hypothesis CURLO : CUR + 32 <= lo.
  Hypothesis DCB : CUR + 32 <= BUF \/ BUF + n <= CUR.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 32 <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKx.
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
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_2S in SM2; unfold A_x509_san_ext_A.STKx in SLO; unfold SEQ_SIZE in *;
    pose proof NRT as (NRTm & NRTf & NRTa);
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation X0 := [(PP, PP + 8); (CUR, CUR + 32)].
  Local Notation NB := (END - P).
  (* [comment removed for export] *)
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Local Notation FSHb := A_x509_san_ext_A.FSHb.
  Local Notation rsl := (A_x509_san_ext_A.rsl CUR).
  Local Notation LF' FB := ((FB, 256) :: LF).
  Local Notation POST := (seq_parser_postE asegs R HIA PHIx FFRx CNTx (fun r => r = 0) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP CUR P END BUF NB lo slo d m mo0).
  Local Notation sfr := (A_x509_san_ext_C.sfr R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m PP CUR P END BUF lo slo bs).
  Local Notation svA := (A_x509_san_ext_C.svA R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP CUR P END BUF lo slo bs).
  Local Notation Wc := (A_x509_san_ext_C.Wc PP).
  Local Notation nLB := (A_x509_san_ext_C.nLB LB).
  Local Notation nfreshA := (A_x509_san_ext_C.nfreshA R LB LF PP CUR).
  Local Notation curFA := (A_x509_san_ext_C.curFA CUR).
  Local Notation headrep := (A_x509_san_ext_C.headrep CUR END BUF).
  Ltac sfr_open D :=
    destruct D as (HHc & HTc & HSc & HCSc & SUBL & SP1 & SP1M & F64 & FRSH & CFB & PRES
                   & FHD & TLc & TSN & FSH & SAVE & RSL & TSB & STb & STlo & PPc & Hpc & BYc & OPP & OBUF & OCUR & CURc & OCc & CURF & MIc & SSc).
  Ltac svA_open D :=
    let S := fresh "SFR" in
    destruct D as (S & HKc & MFc & HFc & HVc & HFRc & SUBN & HND & HFR & HCF & HHD & HLS & CBUF).
  (* [comment removed for export] *)
  Ltac fin_sfr t :=
    unfold A_x509_san_ext_C.sfr;
    spine; first [ eassumption | (unfold A_x509_san_ext_A.FSHb; eassumption) | (unfold A_x509_san_ext_A.rsl; eassumption)
                 | (repeat split; eassumption) | reflexivity | solve [t] | match goal with |- ?g => idtac "SFR-LEFT:" g end ].
  Local Notation ERRQ := (A_x509_san_ext_D.ERRQ R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP CUR P END BUF lo slo bs).
  Local Notation CALLQ1 := (A_x509_san_ext_D.CALLQ1 R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP CUR P END BUF lo slo bs).
  Local Notation EXITP := (A_x509_san_ext_E.EXITP R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP CUR P END BUF lo slo bs).

  (* [comment removed for export] *)
  Hypothesis BUD : havol asegs R HIA h + PHIx NB <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + FFRx NB d <= FR_MAX.
  Hypothesis UW : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d.
  Local Notation KSL := (Z_to_bv 64 CUR) (only parsing).

  Local Notation K0 := (Z_to_bv 64 CUR) (only parsing).
  Local Notation K8 := (Z_to_bv 64 (-9578)) (only parsing).
  Local Notation K16 := (Z_to_bv 64 (-9472)) (only parsing).
  Local Notation K24 := (Z_to_bv 64 (-9570)) (only parsing).
  Local Notation K48 := (Z_to_bv 64 (-8320)) (only parsing).
  Local Notation LoopOb := (A_x509_san_ext_K.LoopOb R HIA PHIp FFRp CNTp h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PP CUR P END BUF lo slo d bs).
  Local Notation PHIy := (A_x509_san_ext_K.PHIy PHIp CNTp).
  Local Notation FFRy := (A_x509_san_ext_K.FFRy FFRp CNTp d).

  #[using="IMG NS1 NA1 AMC CALLOC STKp STKp0 PHIp_mono FFRp_mono CNTp_mono NRT LFB ALP PP0 CWP PPLO HBY BIN B1 B2 B3 B47 B5 B30 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS BUD BUDF UW"] Lemma append_part : forall p0, (forall p', p0 < p' -> LoopOb p') ->
    forall FB sp1 PHIb FFRb w0 w1 w2 tl k0 j64 tg pd Lw p1 jn nodes cur ctc cpc clc cpp mc moc hc
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10v t3 t4 t5 t6 : word),
      svA (nLB nodes) FB sp1 PHIb FFRb w0 w1 w2 tl (Z_to_bv 8 0) k0 K8 K16 K24 K48 j64 tg pd Lw (Z_to_bv 64 p1) jn p1 nodes cur ctc cpc clc cpp 0 mc moc hc ->
      p0 + 2 <= p1 -> p1 + bv_unsigned Lw <= END ->
      PHIb <= PHIy (p1 + bv_unsigned Lw - P) -> FFRb + fr_charge (d + 1) <= FFRy (p1 + bv_unsigned Lw - P) ->
      2 * (Z.of_nat (length nodes) + 1) <= p1 + bv_unsigned Lw - P ->
      aevtA asegs (KF asegs R HIA hc moc) POST
        (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
                 (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 cur) s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
            F (Z_to_bv 64 0xae784) fc None mc (seg_rom asegs)).
  Proof.
    intros p0 IH. intros until t6. intros D HP1 HLE PHI FFR CNT.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0'.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    dpose D as (SFR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CBq).
    dpose SFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpc & _).
    assert (FC0 : 0 <= fr_charge (d + 1)) by (unfold fr_charge; clear - D0'; lia).
    assert (C2 : 0 <= p1 + bv_unsigned Lw - P <= NB) by (clear - Hpc HLE LR B2; lia).
    destruct (A_x509_san_ext_K.bud_top PHIp FFRp CNTp PHIp_mono FFRp_mono CNTp_mono P END d (p1 + bv_unsigned Lw - P) 0 C2 ltac:(clear - C2; lia) D0') as [BT1 BT2].
    assert (CB' : (p1 = 0 /\ bv_unsigned Lw = 0 /\ nodes = []) \/ (BUF <= p1 /\ 0 <= bv_unsigned Lw /\ p1 + bv_unsigned Lw <= END)) by (right; clear - Hpc B1 LR HLE; lia).
    assert (CPR : 0 <= cpp < 2^64) by (clear - CBq B5 B3 B47; destruct CBq as [(-> & _)|(X1 & X2 & X3)]; lia).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA hc moc).
    { eapply A_x509_san_ext_F.seg3 with (STKp := STKp) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs);
        first [ exact SFR | exact CPR | eassumption | match goal with |- ?g => idtac "AP-S3-PRE-LEFT:" g end ]. }
    cbv beta. intros ms3 [(C0 & a0' & a1' & s10' & ->) | (CN0 & ->)].
    - (* [comment removed for export] *)
      idtac "AP-HEAD".
      eapply (aevtA_cut_evtA_KF asegs R HIA hc moc).
      { eapply A_x509_san_ext_F.seg5 with (STKp := STKp) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs);
          first [ exact SFR | exact HLE | eassumption | match goal with |- ?g => idtac "AP-S5-PRE-LEFT:" g end ]. }
      cbv beta. (intros ms5 dd_H; ddestruct dd_H as (mm' & w0' & w1' & w2' & tl' & j64' & jn' & xra' & u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & pc'
                            & -> & PCQ & S5 & PW5)).
      pose proof D as DS.
      eapply (A_x509_san_ext_C.svA_seg R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP CUR P END BUF lo slo bs CWC CURLO D1) in DS; [| exact S5| exact PW5| exact CB'].
      eapply (A_x509_san_ext_K.loop_tail R HIA IMG NS1 NA1 PHIp FFRp CNTp STKp STKp0) with (p0 := p0) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (d := d) (bs := bs);
        first [ exact IH | exact DS | exact PCQ | exact PHI | eassumption
              | lazymatch goal with
                | |- p0 < _ => clear - HP1 LR; lia
                | |- FFRb <= _ => clear - FFR FC0; lia
                | |- 2 * Z.of_nat (length _) <= _ => clear - CNT; lia
                end
              | match goal with |- ?g => idtac "AP-TAIL1-LEFT:" g end ].
    - (* [comment removed for export] *)
      idtac "AP-CALLOC".
      eapply A_x509_san_ext_H.calloc_step with (STKp := STKp) (d := d) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs);
        first [ exact D | eassumption
              | lazymatch goal with
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD PHI BT1; lia
                | |- hfr _ _ _ _ + _ + _ <= FR_MAX => clear - BUDF FFR BT2; lia
                | |- forall _, _ => idtac
                end
              | match goal with |- ?g => idtac "AP-CALLOC-PRE-LEFT:" g end ].
      + (* [comment removed for export] *)
        intros m1 mo1 h1 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 DN.
        idtac "AP-NULL".
        pose proof DN as DN'. destruct DN' as (SFRn & _).
        eapply (aevtA_cut_evtA_KF asegs R HIA h1 mo1).
        { eapply A_x509_san_ext_F.seg4_null with (STKp := STKp) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs);
            first [ exact SFRn | eassumption | match goal with |- ?g => idtac "AP-S4N-PRE-LEFT:" g end ]. }
        cbv beta. intros ms4 EQ.
        eapply A_x509_san_ext_H.err_fin with (STKp := STKp) (d := d) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs);
          first [ exact DN | exact EQ | exact CBq | eassumption
                | lazymatch goal with
                  | |- Z.of_nat (length _) <= _ => unfold A_x509_san_ext_bud.CNTx; apply (A_x509_san_ext_bud.cnt2_div _ (p1 + bv_unsigned Lw - P)); [clear - CNT; lia| clear - C2; lia]
                  | |- PHIb <= _ => clear - PHI BT1; lia
                  | |- FFRb + _ <= _ => clear - FFR BT2; lia
                  end
                | match goal with |- ?g => idtac "AP-ERRFIN-LEFT:" g end ].
      + (* [comment removed for export] *)
        intros m1 mo1 h1 N y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 DY NZ N16 NFR.
        idtac "AP-NODE".
        rt_facts.
        assert (CBR : BUF <= cpp /\ 0 <= clc /\ cpp + clc <= END) by (destruct CBq as [(X & _)|X]; [exfalso; exact (CN0 X)| exact X]).
        pose proof DY as DY'. svA_open DY'. pose proof SFR0 as (HHy & _).
        ddestruct (A_x509_san_ext_C.snoc_facts R HIA h LB LF PP CUR lo slo CWP CWC SLOS SLOL FB (nLB nodes) nodes cur N h1 m1 HHy
                    ltac:(intros b' Hb; apply A_x509_san_ext_C.nLB_sub; exact Hb) ltac:(intros x Hx; apply A_x509_san_ext_C.nLB_in; exact Hx) HND HFR HCF NFR N16)
          as (ND' & HFR' & HCF' & APcur & SUBN').
        dpose (HFR' N ltac:(apply in_or_app; right; left; reflexivity)) as (N0 & _ & NC & NDt & NLB & NPP & NCU & NFB).
        clear HKc MFc HFc HVc HFRc SUBN HND HFR HCF HHD HLS CBUF.
        (* [comment removed for export] *)
        eapply (aevtA_cut_evtA_KF asegs R HIA h1 mo1).
        { eapply A_x509_san_ext_F.seg4_node with (STKp := STKp) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (N := N);
            first [ exact SFR0 | exact NZ | exact N0 | exact NC | exact APcur | exact NPP | exact NFB | eassumption | match goal with |- ?g => idtac "AP-S4Y-PRE-LEFT:" g end ]. }
        cbv beta. (intros ms4 dd_H; ddestruct dd_H as (mm' & w0' & w1' & w2' & tl' & j64' & jn' & a0' & a1' & s10' & -> & S4 & NZ' & PW4)).
        pose proof DY as DS4.
        eapply (A_x509_san_ext_C.svA_seg R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP CUR P END BUF lo slo bs CWC CURLO D1) in DS4; [| exact S4| exact PW4| exact CBq].
        clear Hpc. pose proof DS4 as DS4'. svA_open DS4'. pose proof SFR1 as SFR4. sfr_open SFR1.
        pose proof (A_x509_san_ext_C.headrep_snoc CUR END BUF nodes cur mm' ctc cpc clc cpp N HCF HHD CURc (proj1 CBR) (proj1 (proj2 CBR)) (proj2 (proj2 CBR))) as HHD'.
        pose proof (A_x509_san_ext_C.lseg_snoc R LB LF PP CUR END BUF FB ((N, 32) :: nLB nodes) nodes cur mm' ctc cpc clc cpp N HFR HCF SUBN HLS CURc
                      (proj1 CBR) (proj1 (proj2 CBR)) (proj2 (proj2 CBR))) as HLS'.
        assert (NCELLS : rw_cells asegs mm' N [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
          by (eapply rw_cells_reshape; [exact NZ'| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]).
        pose proof (hm_aobj_block asegs R HIA h1 ((N, 32) :: nLB nodes) _ mm' N 32 HHc ltac:(left; reflexivity)) as ON.
        assert (SFRN : sfr h1 ((N, 32) :: nLB nodes) FB sp1 w0' w1' w2' tl' (Z_to_bv 8 0) k0 K8 K16 K24 K48 j64' tg pd Lw (Z_to_bv 64 p1) jn' p1 N (Z_to_bv 64 0) (Z_to_bv 64 0) 0 0 0 mm').
        { eapply (A_x509_san_ext_K.sfr_swap R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m PP CUR P END BUF lo slo bs); [exact SFR4| exact NCELLS| exact ON|].
          split; [clear - N16; Z.div_mod_to_equations; lia|]. split; [exact N0|]. split; [clear - NC ALO LOS; lia|]. split; [exact NPP|].
          split; [apply NLB; apply in_or_app; left; exact BIN|]. split; [exact NFB|].
          split; [eapply client_wrange_block; [apply in_or_app; left; left; reflexivity| clear; lia| clear; lia]|].
          eapply (wcover_fresh R); [exact (A_x509_san_ext_C.nodeF_fresh R LB LF PP CUR FB N (HFR' N ltac:(apply in_or_app; right; left; reflexivity)))| clear; lia| clear; lia| clear - ALO LOS SLO NS1 NA1 NRTa STKp0; lia]. }
        (* [comment removed for export] *)
        eapply (aevtA_cut_evtA_KF asegs R HIA h1 mo1).
        { eapply A_x509_san_ext_F.seg5 with (STKp := STKp) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (c := N);
            first [ exact SFRN | exact HLE | eassumption | match goal with |- ?g => idtac "AP-S5Y-PRE-LEFT:" g end ]. }
        cbv beta. (intros ms5 dd_H; ddestruct dd_H as (mm2 & w0'' & w1'' & w2'' & tl'' & j64'' & jn'' & xra' & u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & pc'
                              & -> & PCQ & S5 & PW5)).
        destruct (A_x509_san_ext_C.nrep_move R HIA h LB LF sp PP CUR END BUF lo CWC CURLO D1 FB ((N, 32) :: nLB nodes) (nodes ++ [N]) N h1 _ mm' mm' mm2
                    HHc SUBN' ltac:(intros b' Hb; right; apply A_x509_san_ext_C.nLB_sub; exact Hb) ND' HFR' HCF' PW5 HHD' HLS') as [HHD2 HLS2].
        assert (DF : svA (nLB (nodes ++ [N])) FB sp1 PHIb (FFRb + fr_charge (d + 1)) w0'' w1'' w2'' tl'' (Z_to_bv 8 248) k0 K8 K16 K24 K48 j64'' tg pd Lw (Z_to_bv 64 p1) jn''
                       (p1 + bv_unsigned Lw) (nodes ++ [N]) N tg pd (bv_unsigned Lw) p1 0 mm2 mo1 h1).
        { rewrite A_x509_san_ext_C.nLB_snoc.
          split; [exact S5|]. split; [exact HKc|]. split; [exact MFc|]. split; [exact HFc|]. split; [exact HVc|]. split; [exact HFRc|].
          split; [exact SUBN'|]. split; [exact ND'|]. split; [exact HFR'|]. split; [exact HCF'|]. split; [exact HHD2|]. split; [exact HLS2|].
          right. clear - Hpc B1 LR HLE. lia. }
        eapply (A_x509_san_ext_K.loop_tail R HIA IMG NS1 NA1 PHIp FFRp CNTp STKp STKp0) with (p0 := p0) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (d := d);
          first [ exact IH | exact DF | exact PCQ | exact PHI | exact FFR | eassumption
                | lazymatch goal with
                  | |- p0 < _ => clear - HP1 LR; lia
                  | |- 2 * Z.of_nat (length _) <= _ => rewrite length_app; cbn [length]; clear - CNT; lia
                  end
                | match goal with |- ?g => idtac "AP-TAIL2-LEFT:" g end ].
  Qed.
  End Call.
End Walk.
