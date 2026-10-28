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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_san_ext_A A_x509_san_ext_bud A_x509_san_ext_B A_x509_san_ext_C A_x509_san_ext_D A_x509_san_ext_E A_x509_san_ext_F A_x509_san_ext_G A_x509_san_ext_H.
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

  #[using="IMG NS1 NA1 HMND STKp STKp0 PSAN NRT LFB CWP PPLO BIN B1 B3 B47 B5 B30 ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW"] Lemma psan_step : forall FB sp1 PHIa FFRa w0 w1 w2 tl k0 k8 k16 k24 k48 j64 tg pd Lw p1 nodes cur ctc cpc clc cpp cnx mc moc hc (Q : config -> Prop)
      (xra t0 t1 t2 a2 a3 a4 a5 a6 a7 s10v t3 t4 t5 t6 : word),
    svA (nLB nodes) FB sp1 PHIa FFRa w0 w1 w2 tl (Z_to_bv 8 0) k0 k8 k16 k24 k48 j64 tg pd Lw (Z_to_bv 64 p1) (repeat (Z_to_bv 8 0) 80) p1 nodes cur ctc cpc clc cpp cnx mc moc hc ->
    p1 + bv_unsigned Lw <= END ->
    havol asegs R HIA h + PHIa + PHIp (bv_unsigned Lw) <= AVOL_MAX -> hfr asegs R HIA h + FFRa + FFRp (bv_unsigned Lw) (d + 1) <= FR_MAX ->
    (forall m1 mo1 h1 (nn : list Z) (r t dn : Z) (rest : list cell) (jn' : list byte) (y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
        svA (SNAME (rev nn) ++ nLB nodes) FB sp1 (PHIa + PHIp (bv_unsigned Lw)) (FFRa + FFRp (bv_unsigned Lw) (d + 1)) w0 w1 w2 tl (Z_to_bv 8 0) k0 k8 k16 k24 k48 j64 tg pd Lw (Z_to_bv 64 p1)
            jn' p1 nodes cur ctc cpc clc cpp cnx m1 mo1 h1 ->
        rw_cells asegs m1 (FB + 64) (C4 (Z_to_bv 64 t) :: rest) -> 0 <= t <= 7 ->
        (t = 4 -> exists p4 j48 mg pad7 j8, rest = CB 4 p4 :: name_blob j48 dn mg pad7 ++ [CB 8 j8]) ->
        (t = 4 -> name_chain asegs (fun _ => True) m1 (SNAME (rev nn) ++ nLB nodes) dn nn) ->
        (t <> 4 -> nn = []) -> (r <> 0 -> nn = []) -> List.NoDup nn -> Z.of_nat (length nn) <= CNTp (bv_unsigned Lw) ->
        -0x3000 < r <= 0 ->
        aevtA asegs (KF asegs R HIA h1 mo1) Q
          (MS (mkR (Z_to_bv 64 0xae764) (Z_to_bv 64 sp1) gp tp y0 y1 y2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                   (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
                   (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 cur) s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) y3 y4 y5 y6)
              F (Z_to_bv 64 0xae764) fc None m1 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc moc) Q
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 (sp1 + 96)) (Z_to_bv 64 (FB + 64)) a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 cur) s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
          F (Z_to_bv 64 0xae760) fc None mc (seg_rom asegs)).
  Proof.
    intros until t6. intros D HLE BUDc BUDFc KC. pose proof D as D0. svA_open D. sfr_open SFR.
    rt_facts;
    pose proof (hcs_ok asegs R HIA hc) as CSOKc;
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HTOP; rewrite HTc, HSc in HTOP;
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NA1 NRTa STKp0; lia);
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 NA1 NRTa STKp0 TOP HTOP; lia]);
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSc| exact SCS]);
    assert (SCS1 : crange (hcs asegs R HIA hc) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]);
    assert (SCS03 : crange (hcs asegs R HIA hc) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSc| exact SCS0]);
    assert (CFBc : crange (hcs asegs R HIA hc) FB 256) by (eapply crange_mono; [exact HCSc| exact CFB]);
    lazymatch type of HHc with HM _ _ _ _ ?Lh _ ?mm =>
      pose proof (fresh_apart_relist R HIA LF hc LB Lh mm FB 256 FRSH HHc) as FRSHc;
      ddestruct (frame_factsA R HIA (hcs asegs R HIA hc) hc Lh LF mm FB 256 lo HHc eq_refl FRSHc F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (_ & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS); change (256 / 8) with 32 in SBND, APS;
      assert (BINh : In (BUF, n) Lh) by (apply SUBL; exact BIN);
      assert (APB : FB + 256 <= BUF \/ BUF + n <= FB) by (apply F3; apply in_app_iff; left; exact BINh);
      assert (BINA : In (BUF, n) (Lh ++ fdata (LF' FB))) by (apply in_app_iff; left; exact BINh);
      assert (BUFLO : BUF + n <= lo) by
        (destruct (blocks_below_hm R HIA hc Lh _ mm Lh HHc ltac:(intros b' Hb; exact Hb) _ BINh) as [_ BCE]; cbn [fst snd] in BCE; clear - BCE ALO LOS; lia);
      assert (SUBq : forall b', In b' (LB ++ fdata LF) -> In b' (Lh ++ fdata (LF' FB))) by
        (intros b' Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; exact (SUBL b' Hb)| right; apply (fdata_cons_sub b' [] FB 256 LF); exact Hb]);
      assert (CWP1 : client_wrange L (Lh ++ fdata (LF' FB)) lo (htop asegs R HIA h) PP 8) by (eapply client_wrange_mono; [exact CWP| exact SUBq]);
      pose proof CWP1 as CWP1c; rewrite <- HTc in CWP1c;
      lazymatch type of CURc with rw_cells _ _ ?cur _ =>
        pose proof (presW_init_at R HIA hc _ _ Lh LF mm (bv_unsigned sp) (bv_unsigned sp) (Wc cur) hc HHc
                      ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear - LOS SLO NS1 NA1 NRTa STKp0; lia)) as PRESw;
        assert (WCPw : wcover R Lh LF (bv_unsigned sp) (Wc cur) PP 8) by (apply wcover_inside; cbn [inside A_x509_san_ext_C.Wc]; left; clear; lia);
        assert (WCCw : wcover R Lh LF (bv_unsigned sp) (Wc cur) cur 32) by (apply wcover_inside; cbn [inside A_x509_san_ext_C.Wc]; right; left; clear; lia)
      end;
      assert (WLw : wlow R Lh LF) by (split; [exact (proj2 (proj2 (proj2 PRESw)))| apply (art_data_lo asegs R HIA)])
    end;
    pose proof (art_stk_high asegs R HIA) as STKH;
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP;
    pose proof (frame_apart_obj R HIA LB LF lo _ CUR 32 FB 256 FRSH CWC ltac:(clear; lia) ltac:(clear; lia) LOS) as APC;
    ddestruct CURF as (CAL & CPOS & CLO & CPP & CBF & CFBa & CWcur & WCC0);
    pose proof CWcur as CWcurc; rewrite <- HTc in CWcurc;
    assert (WL0 : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]);
    assert (WCP0 : wcover R LB LF (bv_unsigned sp) X0 PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia);
    unfold A_x509_san_ext_A.FSHb in FSH; unfold A_x509_san_ext_A.rsl in RSL.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0'.
    assert (UW1 : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA hc) (bv_unsigned sp) sp1 (d + 1)).
    { assert (UWa : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA hc) (bv_unsigned s0) (bv_unsigned sp) d).
      { eapply (uwc_presA R); [exact (presW_presA asegs R HIA hc LB LF _ _ _ _ _ PRES)| rewrite HSc; exact UW| clear; lia| | clear - SPR; lia| rewrite HSc; apply hstkhi_le64; clear - LOS SLO SPR NS1 NA1 NRTa STKp0; lia].
        intros a Ha. cbn [outside]. split; [| split; [| exact I]]; clear - Ha PPLO CURLO SLO NS1 NA1 NRTa STKp0; lia. }
      pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UWa| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0']. }
    destruct (sshad_split asegs AL mc slo sp1 (bv_unsigned sp) SSc ltac:(clear - SP1 SLO SLOL NS1 NA1 NRTa STKp0; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSlo SShi].
    assert (OSB : aobj asegs AL (hcs asegs R HIA hc) mc (sp1 + 96) 24).
    { change 24 with (8 * Z.of_nat 3).
      eapply (aobj_of_zero_shadow asegs AL (hcs asegs R HIA hc) mc (sp1 + 96) (zcells 3) (sp1 + 96) 0 3 CSOKc);
        [ eapply crange_sub; [exact SCSc| clear - SP1 SLO NS1 NA1 NRTa STKp0; lia| clear - SP1; lia]
        | clear - SP1M; Z.div_mod_to_equations; lia | clear; lia
        | apply (sshad_chunk asegs AL mc slo (bv_unsigned sp) 2 (sp1 + 96) SSc); [clear - SP1 SLO SLOL NS1 NA1 NRTa STKp0; lia| clear - SP1; lia| clear - SP1M; Z.div_mod_to_equations; lia]
        | intros i Hi; do 3 (destruct i as [|i]; [reflexivity| try (exfalso; clear - Hi; lia)]); exfalso; clear - Hi; lia ]. }
    assert (OSAN : aobj asegs AL (hcs asegs R HIA hc) mc (FB + 64) 80).
    { change 80 with (8 * Z.of_nat 10). eapply (aobj_of_zero_shadow_sh asegs AL (hcs asegs R HIA hc) mc FB _ (FB + 64) 8 10 CSOKc FSH);
        [ eapply crange_sub; [exact CFBc| clear; lia| clear; lia] | exact F8 | clear - F0; lia | clear; lia
        | intros i Hi; do 10 (destruct i as [|i]; [reflexivity| try (exfalso; clear - Hi; lia)]); exfalso; clear - Hi; lia ]. }
    assert (CWN : client_wrange L (nLB nodes ++ fdata (LF' FB)) lo (htop asegs R HIA hc) (FB + 64) 80) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    assert (TSBb : rw_cells asegs mc (sp1 + 96) (buf_cells tg pd (bv_unsigned Lw) p1)) by (unfold buf_cells; rewrite Z_to_bv_bv_unsigned; exact TSB).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep.
    idtac "PSAN-CALL".
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply PSAN with (h := hc) (LB := nLB nodes) (LF := LF' FB) (SB := sp1 + 96) (SAN := FB + 64) (BUF := BUF) (sp0 := p1) (slen := bv_unsigned Lw) (lo := lo) (slo := slo) (d := d + 1)
                       (bs := bs) (tgw := tg) (pdw := pd);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HHc | exact HK1 | exact TSBb | exact OSB | exact OSAN | exact TSN | exact CWN | exact BYc | exact STlo | exact SSlo | exact SLOS | exact SLOL | exact MIc | exact TPV | exact UW1
              | exact B47 | exact B5 | exact B30 | exact BINh | reflexivity
              | lazymatch goal with
                | |- (length _ <= _)%nat => cbn [length]; clear - LFB; lia
                | |- List.NoDup _ => exact (HMND _ _ _ _ HHc)
                | |- client_range _ _ _ (sp1 + 96) _ => apply client_range_stack; clear - SP1 SLO NS1 NA1 NRTa STKp0; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUDc HVc; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDFc HFRc; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                | |- _ mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- _ mod 8 = 0 => clear - SP1M F8; Z.div_mod_to_equations; lia
                | |- _ => clear - SP1 SP1M SLO NS1 NA1 NRTa STKp0 F0 FBLO APB BUFLO SPH HLE LR Hpc B1 B3; lia
                end
              | match goal with |- ?g => idtac "PSAN-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    idtac "PSAN-POST".
    ddestruct PO as (q0 & q1 & q2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m4 & mo4' & h3 & r3 & t & dn & rest & nn
                    & E4 & Ea0 & Hr3 & MI4 & ST4 & SS4 & MF4 & HP4 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HCNT3 & HSAN4 & SZR & TR & T4 & NC4 & TN4 & RN4 & ND4 & APN4 & HH4).
    injection E4 as Ems Emo. subst ms4 mo4 qa0.
    replace (ret_pc (Z_to_bv 64 0xae764)) with (Z_to_bv 64 0xae764 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST4, SS4, HP4 by exact SP1R.
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo4') _ _ _ (conj HK3 (mo_frame_refl mo4'))).
    (* [comment removed for export] *)
    assert (HPw : presA asegs R LB LF sp1 sp1 (hstkhi asegs R HIA hc) [] mc m4).
    { eapply (presA_drop_fresh_gen R LB LF _ _ _ [] FB 256 (FB + 64) (FB + 64 + 80)); [| exact FRSH| clear; lia| clear; lia| clear - ALO LOS SLO SP1 NS1 NA1 NRTa STKp0; lia].
      eapply presA_weaken; [exact HP4| intros b' Hb; apply A_x509_san_ext_C.nLB_sub; exact Hb| intros b' Hb; right; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    assert (SZC : cells_size (C4 (Z_to_bv 64 t) :: rest) = 80%nat) by (cbn [cells_size csize]; clear - SZR; lia).
    pose proof HSAN4 as TSN4. apply A_x509_san_ext_F.rw_cells_blob' in TSN4. rewrite SZC in TSN4.
    assert (SShi4 : sshad asegs AL m4 sp1 (bv_unsigned sp)).
    { eapply (presA_sshad asegs R); [exact HP4| exact SShi| clear; lia| rewrite HSc; clear - HTOP TOP; lia]. }
    pose proof (sshad_merge asegs AL m4 slo sp1 (bv_unsigned sp) SS4 SShi4 ltac:(clear - SP1 SLOL SLO NS1 NA1 NRTa STKp0; lia)) as SSm4.
    eapply (KC m4 mo4' h3 nn r3 t dn rest);
      first [ exact HSAN4 | exact TR | exact T4 | exact NC4 | exact TN4 | exact RN4 | exact ND4 | exact HCNT3 | exact Hr3
            | match goal with |- svA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac end
            | idtac ].
    eapply (A_x509_san_ext_C.svA_callG R HIA IMG NS1 NA1 STKp STKp0) with (Lp := nLB nodes) (Lh := nLB nodes) (SSPq := sp1) (Wq := [(FB + 64, FB + 64 + 80)]) (mc := mc) (moc := moc) (hc := hc);
      first [ exact D0 | exact HP4 | exact HPw | exact MI4 | exact ST4 | exact SSm4 | exact TSN4 | exact HT3 | exact HS3 | exact HF3 | exact HK3 | exact HCS3 | exact HV3 | exact HFR3 | exact HH4
            | exact (mo_frame_trans _ _ _ MF1 MF4) | eassumption
            | lazymatch goal with
              | |- sp1 <= sp1 => clear; lia
              | |- forall A k, _ -> disjoint_from _ A k => intros A k HA; cbn [disjoint_from]; clear - HA; lia
              | |- forall b', In b' LB -> In b' (nLB _) => intros b' Hb; apply A_x509_san_ext_C.nLB_sub; exact Hb
              | |- forall x, In x nodes -> In (x, 32) (nLB _) => intros x Hx; apply A_x509_san_ext_C.nLB_in; exact Hx
              | |- forall b', In b' LB -> In b' (_ ++ nLB _) => intros b' Hb; apply in_or_app; right; apply A_x509_san_ext_C.nLB_sub; exact Hb
              | |- forall x, In x nodes -> In (x, 32) (_ ++ nLB _) => intros x Hx; apply in_or_app; right; apply A_x509_san_ext_C.nLB_in; exact Hx
              end
            | match goal with |- ?g => idtac "PSAN-G-LEFT:" g end ].
  Qed.
  End Call.
End Walk.
