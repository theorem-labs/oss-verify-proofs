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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_san_ext_A A_x509_san_ext_bud A_x509_san_ext_B A_x509_san_ext_C A_x509_san_ext_D A_x509_san_ext_E A_x509_san_ext_F A_x509_san_ext_G.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
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

  #[using="Type"] Lemma svA_mo : forall Lh FB sp1 PHIa FFRa w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn p nodes cur ctc cpc clc cpp cnx mc moc hc mo',
    svA Lh FB sp1 PHIa FFRa w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn p nodes cur ctc cpc clc cpp cnx mc moc hc ->
    HK asegs R HIA hc mo' -> mo_frame moc mo' ->
    svA Lh FB sp1 PHIa FFRa w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn p nodes cur ctc cpc clc cpp cnx mc mo' hc.
  Proof.
    intros until mo'. intros D HK' MF'. svA_open D.
    split; [exact SFR|]. split; [exact HK'|]. split; [eapply mo_frame_trans; [exact MFc| exact MF']|].
    spine; assumption.
  Qed.

  
  (* [comment removed for export] *)
  #[using="IMG NS1 NA1 STKp STKp0 LFB CWP PPLO CUR0 CWC CURLO D1 SLOS SLOL SLO TOP SPH"] Lemma exitp_fin : forall FB sp1 PHIa FFRa w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn p nodes cur ctc cpc clc cpp cnx mc moc hc
      (ctc' cpc' : word) (clc' cpp' : Z) ms,
    svA (nLB nodes) FB sp1 PHIa FFRa w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn p nodes cur ctc cpc clc cpp cnx mc moc hc ->
    EXITP hc (nLB nodes) FB sp1 k0 k8 k16 k24 k48 cur ctc' cpc' clc' cpp' 0 mc ms ->
    ((cpp' = 0 /\ clc' = 0 /\ nodes = []) \/ (BUF <= cpp' /\ 0 <= clc' /\ cpp' + clc' <= END)) ->
    Z.of_nat (length nodes) <= CNTx NB -> PHIa <= PHIx NB -> FFRa <= FFRx NB d ->
    aevtA asegs (KF asegs R HIA hc moc) POST ms.
  Proof.
    intros until ms. intros D EX CB' CNT PHI FFR.
    ddestruct EX as (mm & r & p' & w0' & w1' & w2' & tl' & tg' & pd' & ln' & pv' & j64' & jn'
                    & xra & t0 & t1 & t2 & a0 & a3 & a4 & a5 & a6 & a7 & s3v & s4v & s5v & s6v & s7v & s8v & s9v & s10v & t3 & t4 & t5 & t6
                    & -> & Hr & S1 & PW & HEQ).
    pose proof D as DS.
    eapply (A_x509_san_ext_C.svA_seg R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP CUR P END BUF lo slo bs CWC CURLO D1) in DS; [| exact S1| exact PW| exact CB'].
    intros mo1 [HK1 MF1].
    eapply (A_x509_san_ext_C.ret_walk R HIA IMG NS1 NA1 PHIp FFRp CNTp STKp STKp0) with (bs := bs);
      first [ (eapply svA_mo; [exact DS| exact HK1| exact MF1]) | eassumption | match goal with |- ?g => idtac "EXF-LEFT:" g end ].
  Qed.

  (* [comment removed for export] *)
  #[using="IMG NS1 NA1 STKp STKp0 LFB PP0 CWP PPLO HBY BIN B3 B47 B30 DPB CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH"] Lemma err_fin : forall FB sp1 PHIa FFRa w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn p nodes cur ctc cpc clc cpp cnx mc moc hc
      (ctc' cpc' : word) (clc' cpp' : Z) ms,
    svA (nLB nodes) FB sp1 PHIa FFRa w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn p nodes cur ctc cpc clc cpp cnx mc moc hc ->
    ERRQ hc (nLB nodes) FB sp1 k0 k8 k16 k24 k48 cur ctc' cpc' clc' cpp' 0 mc ms ->
    ((cpp' = 0 /\ clc' = 0 /\ nodes = []) \/ (BUF <= cpp' /\ 0 <= clc' /\ cpp' + clc' <= END)) ->
    Z.of_nat (length nodes) <= CNTx NB -> PHIa <= PHIx NB -> FFRa <= FFRx NB d ->
    aevtA asegs (KF asegs R HIA hc moc) POST ms.
  Proof.
    intros until ms. intros D EQ CB' CNT PHI FFR.
    ddestruct EQ as (mm & r & p' & w0' & w1' & w2' & tl' & tg' & pd' & ln' & pv' & j64' & jn'
                    & xra & t0 & t1 & t2 & a0 & a3 & a4 & a5 & a6 & a7 & s3v & s4v & s5v & s6v & s7v & s8v & s9v & s10v & t3 & t4 & t5 & t6
                    & -> & Hr & S1 & PW).
    pose proof D as DS.
    eapply (A_x509_san_ext_C.svA_seg R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP CUR P END BUF lo slo bs CWC CURLO D1) in DS; [| exact S1| exact PW| exact CB'].
    eapply (aevtA_cut_evtA_KF asegs R HIA hc moc).
    { eapply A_x509_san_ext_E.err_walk with (STKp := STKp) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (r := r); first [ exact S1 | eassumption | (clear - Hr; lia) | match goal with |- ?g => idtac "ERRF-PRE-LEFT:" g end ]. }
    cbv beta. intros ms2 EX.
    eapply exitp_fin; [exact DS| exact EX| exact CB'| exact CNT| exact PHI| exact FFR].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG NS1 NA1 CALLOC STKp STKp0 NRT CWP PPLO BIN ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA TPV LOS UW"] Lemma calloc_step : forall FB sp1 PHIa FFRa w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn p nodes cur ctc cpc clc cpp cnx mc moc hc (Q : config -> Prop)
      (xra t0 t1 t2 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6 : word),
    svA (nLB nodes) FB sp1 PHIa FFRa w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn p nodes cur ctc cpc clc cpp cnx mc moc hc ->
    havol asegs R HIA h + PHIa <= AVOL_MAX -> hfr asegs R HIA h + FFRa + fr_charge (d + 1) <= FR_MAX ->
    (forall m1 mo1 h1 (y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
        svA (nLB nodes) FB sp1 PHIa (FFRa + fr_charge (d + 1)) w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn p nodes cur ctc cpc clc cpp cnx m1 mo1 h1 ->
        aevtA asegs (KF asegs R HIA h1 mo1) Q
          (MS (mkR (Z_to_bv 64 0xae7d4) (Z_to_bv 64 sp1) gp tp y0 y1 y2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 0) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                   s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v y3 y4 y5 y6)
              F (Z_to_bv 64 0xae7d4) fc None m1 (seg_rom asegs))) ->
    (forall m1 mo1 h1 (N : Z) (y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
        svA ((N, 32) :: nLB nodes) FB sp1 PHIa (FFRa + fr_charge (d + 1)) w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn p nodes cur ctc cpc clc cpp cnx m1 mo1 h1 ->
        rw_cells asegs m1 N [CB 32 (repeat (Z_to_bv 8 0) 32)] -> N mod 16 = 0 ->
        fresh_apart R (nLB nodes) (LF' FB) N 32 ->
        aevtA asegs (KF asegs R HIA h1 mo1) Q
          (MS (mkR (Z_to_bv 64 0xae7d4) (Z_to_bv 64 sp1) gp tp y0 y1 y2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 N) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                   s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v y3 y4 y5 y6)
              F (Z_to_bv 64 0xae7d4) fc None m1 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc moc) Q
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 1) (Z_to_bv 64 32) a2 a3 a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
          F (Z_to_bv 64 0xae7d0) fc None mc (seg_rom asegs)).
  Proof.
    intros until t6. intros D BUDc BUDFc KN KY. pose proof D as D0. svA_open D. sfr_open SFR. rt_facts.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT. rewrite HTc, HSc in HT.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NA1 NRTa STKp0; lia).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0'.
    assert (UW1 : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA hc) (bv_unsigned sp) sp1 (d + 1)).
    { assert (UWa : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA hc) (bv_unsigned s0) (bv_unsigned sp) d).
      { eapply (uwc_presA R); [exact (presW_presA asegs R HIA hc LB LF _ _ _ _ _ PRES)| rewrite HSc; exact UW| clear; lia| | clear - SPR; lia| rewrite HSc; apply hstkhi_le64; clear - LOS SLO SPR NS1 NA1 NRTa STKp0; lia].
        intros a Ha. cbn [outside]. split; [| split; [| exact I]]; clear - Ha PPLO CURLO SLO NS1 NA1 NRTa STKp0; lia. }
      pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UWa| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0']. }
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep.
    replace (Z_to_bv 64 431236 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc_t asegs R HIA) with (h := hc) (LB := nLB nodes) (LF := LF' FB) (cnt := 1) (sz := 32) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HHc | exact HK1 | exact LOS | exact TPV | exact UW1 | exact STlo | exact MIc | reflexivity
              | lazymatch goal with
                | |- lo <= sp1 - arl_need_malloc R => clear - SLO SP1 NS1 NA1 NRTm NRTa STKp0; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- 0 <= 1 => clear; lia
                | |- 0 <= 32 => clear; lia
                | |- 1 * 32 < AMAX => unfold AMAX; clear; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => rewrite (vchg_small (1 * 32)) by (unfold AMAX_SEC; clear; lia); clear - BUDc HVc; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDFc HFRc; lia
                end
              | c24_lit   (* [comment removed for export] *)
              | match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms2 mo2x dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2' & mo2 & E2 & PO). injection E2 as Ems Emo. subst ms2' mo2x.
    unfold call_postA in PO. cbv beta in PO.
    ddestruct PO as (u0 & u1 & u2 & r & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & Ems2 & MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    subst ms2.
    rewrite ?(unsigned_lit sp1) in ST2 by exact SP1R. rewrite ?(unsigned_lit sp1) in HP2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 0xae7d4)) with (Z_to_bv 64 0xae7d4 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (vchg_small (1 * 32)) in HV2 by (unfold AMAX_SEC; clear; lia). rewrite ?Z.mul_1_l in CASES.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo2) _ _ _ (conj HK2 (mo_frame_refl mo2))).
    assert (HPw : presA asegs R LB LF sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m2).
    { eapply presA_weaken; [exact HP2| intros b' Hb; apply A_x509_san_ext_C.nLB_sub; exact Hb| intros b' Hb; right; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    assert (TSN2 : rw_cells asegs m2 (FB + 64) [CB 80 jn]).
    { eapply (presA_rw_cells asegs R); [exact HP2| exact TSN| | exact I]. cbn [cells_size csize Nat.add length].
      eapply client_range_block; [apply in_or_app; right; cbn; right; left; reflexivity| clear; lia| clear; lia]. }
    assert (SS2 : sshad asegs AL m2 slo (bv_unsigned sp)).
    { eapply (presA_sshad asegs R); [exact HP2| exact SSc| exact SLOS| rewrite HSc; clear - HT TOP; lia]. }
    destruct CASES as [[Er HH2] | (N & Er & NAL & NFR & NSTK & HH2 & NZ)]; subst r.
    - eapply KN.
      replace PHIa with (PHIa + 0) by (clear; lia).
      eapply (A_x509_san_ext_C.svA_callG R HIA IMG NS1 NA1 STKp STKp0) with (Lp := nLB nodes) (Lh := nLB nodes) (SSPq := arl_stklo R) (Wq := @nil ivl) (mc := mc) (moc := moc) (hc := hc);
        first [ exact D0 | exact HP2 | exact HPw | exact MI2 | exact ST2 | exact SS2 | exact TSN2 | exact HT2 | exact HS2 | exact HF2 | exact HK2 | exact HCS2 | exact HV2 | exact HFR2 | exact HH2
              | exact (mo_frame_trans _ _ _ MF1 MF2) | eassumption
              | lazymatch goal with
                | |- arl_stklo R <= sp1 => clear - LOS SLO SP1 NS1 NA1 NRTa STKp0; lia
                | |- forall A k, _ -> disjoint_from [] A k => intros A k _; exact I
                | |- forall b', In b' LB -> In b' (nLB _) => intros b' Hb; apply A_x509_san_ext_C.nLB_sub; exact Hb
                | |- forall x, In x nodes -> In (x, 32) (nLB _) => intros x Hx; apply A_x509_san_ext_C.nLB_in; exact Hx
                end
              | match goal with |- ?g => idtac "GC0N-LEFT:" g end ].
    - eapply (KY m2 mo2 h2 N).
      + replace PHIa with (PHIa + 0) by (clear; lia).
        eapply (A_x509_san_ext_C.svA_callG R HIA IMG NS1 NA1 STKp STKp0) with (Lp := nLB nodes) (Lh := nLB nodes) (SSPq := arl_stklo R) (Wq := @nil ivl) (mc := mc) (moc := moc) (hc := hc);
          first [ exact D0 | exact HP2 | exact HPw | exact MI2 | exact ST2 | exact SS2 | exact TSN2 | exact HT2 | exact HS2 | exact HF2 | exact HK2 | exact HCS2 | exact HV2 | exact HFR2 | exact HH2
                | exact (mo_frame_trans _ _ _ MF1 MF2) | eassumption
                | lazymatch goal with
                  | |- arl_stklo R <= sp1 => clear - LOS SLO SP1 NS1 NA1 NRTa STKp0; lia
                  | |- forall A k, _ -> disjoint_from [] A k => intros A k _; exact I
                  | |- forall b', In b' LB -> In b' (nLB _) => intros b' Hb; apply A_x509_san_ext_C.nLB_sub; exact Hb
                  | |- forall x, In x nodes -> In (x, 32) (nLB _) => intros x Hx; apply A_x509_san_ext_C.nLB_in; exact Hx
                  | |- forall b', In b' LB -> In b' (_ :: nLB _) => intros b' Hb; right; apply A_x509_san_ext_C.nLB_sub; exact Hb
                  | |- forall x, In x nodes -> In (x, 32) (_ :: nLB _) => intros x Hx; right; apply A_x509_san_ext_C.nLB_in; exact Hx
                  end
                | match goal with |- ?g => idtac "GC0Y-LEFT:" g end ].
      + exact NZ.
      + exact NAL.
      + exact NFR.
  Qed.
  End Call.
End Walk.
