(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_x509_get_name_A.     (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_len
     A_asn1_free_named_data_list_shallow A_crt_stmts A_crt_parse_stmts A_pkcs7_getcerts A_mpi_stmtA A_x509_get_name_stmt A_x509_get_name_stmtE A_x509_get_name_A A_x509_get_name_B A_x509_get_name_C A_x509_get_name_D A_x509_get_name_E A_x509_get_name_F A_x509_get_name_G.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw TacA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
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
  Hypothesis SM1 : arl_smalloc R 1 = A_SMALLOC_1.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis CALLOC : arl_calloc R = A_WCALLOC.
  Hypothesis FREE : arl_free R = A_WFREE.
  (* [comment removed for export] *)
  Hypothesis GETTAG : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_G.
  Hypothesis FREEL : asn1_free_named_data_list_shallow_stmtA asegs R HIA A_ASN1_FREE_NAMED_DATA_LIST_SHALLOW.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55855578687.12000003S1R". (* [comment removed for export] *)
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Notation STKn := (A_x509_get_name_A.STKn R).
  Local Notation CNTn := A_x509_get_name_A.CNTn.
  Local Notation PHIn := A_x509_get_name_A.PHIn.
  Local Notation FFRn := A_x509_get_name_A.FFRn.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP P END BUF CUR lo slo d : Z) (bs : list byte) (j48 : list byte) (mg : byte) (pad7 : list byte).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 7)%nat.
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
  Hypothesis HCUR : rw_cells asegs m CUR (name_blob j48 0 mg pad7).
  Hypothesis ALC : CUR mod 8 = 0.
  Hypothesis CUR0 : 0 < CUR.
  Hypothesis CWC : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CUR 64.
  Hypothesis CURLO : CUR + 64 <= lo.
  Hypothesis DCB : CUR + 64 <= BUF \/ BUF + n <= CUR.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 64 <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKn.
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
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_1 in SM1; unfold A_x509_get_name_A.STKn in SLO; unfold NAME_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation FSH0 :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Local Notation X0 := [(PP, PP + 8); (CUR, CUR + 64)].
  Local Notation NB := (END - P).
  Local Notation POST := (x509_get_name_postE asegs R HIA PHIn FFRn CNTn h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP CUR P END NB lo slo d m mo0).
  Local Notation nvA := (nvA R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP END BUF CUR lo slo bs).
  Local Notation nLB := (nLB LB).
  Local Notation nfreshA := (nfreshA R LB LF PP CUR).
  Local Notation curFA := (curFA CUR).
  Local Notation headrep := (headrep CUR).
  Local Notation Wc := (Wc PP).

  Ltac nvA_open D :=
    destruct D as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & PRES & SP1 & SP1M & F64 & FRSH & CFB
                   & FHD & GA & GB & FSH & SAVE & RSL & STb & STlo & BYc & OPP & OCUR & OBUF & MIc & SSc
                   & SUBL & SUBN & HND & HFR & HCF & HHD & HLS & OCc);
    unfold A_x509_get_name_C.FSHb in FSH; unfold A_x509_get_name_A.rsl in RSL.
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  (* [comment removed for export] *)
  Ltac sec_hyps :=
    first [ exact IMG | exact UARG | exact SM1 | exact NS1 | exact DIMG | exact HMND | exact CALLOC | exact FREE | exact GETTAG | exact FREEL
          | exact LFB | exact HPP | exact ALP | exact PP0 | exact CWP | exact PPLO | exact HBY | exact BIN | exact B1 | exact B2 | exact B3 | exact B47 | exact B5 | exact B30 | exact DPB
          | exact HCUR | exact ALC | exact CUR0 | exact CWC | exact CURLO | exact DCB | exact D1
          | exact SLOS | exact SLOL | exact SLO | exact TOP | exact SPA | exact SPH | exact TPV | exact NDL ].

  (* [comment removed for export] *)
  Ltac walk_prep :=
    lazymatch goal with HHc : HM _ _ _ ?hc ?Lh ((?FB, 128) :: LF) ?mc, HTc : htop _ _ _ ?hc = _, HSc : hstkhi _ _ _ ?hc = _, HCSc : forall x, CS x -> hcs _ _ _ ?hc x,
                        CFB : crange CS ?FB 128, FRSH : fresh_apart R LB LF ?FB 128, OPP : aobj _ _ _ ?mc PP 8, OCUR : aobj _ _ _ ?mc CUR 64, OBUF : aobj _ _ _ ?mc BUF n,
                        PRES : presW _ _ _ ?hc LB LF _ _ _ m ?mc, SCS0 : crange CS (arl_stklo R) _, SUBL : forall b, In b LB -> In b ?Lh |- _ =>
      pose proof (hcs_ok asegs R HIA hc) as CSOKc;
      pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT; rewrite HTc, HSc in HT;
      pose proof (crange_mono _ _ _ _ HCSc CFB) as CFBc;
      pose proof (crange_mono _ _ _ _ HCSc SCS0) as SCS03c;
      assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 NRT TOP HT; lia]);
      pose proof (crange_mono _ _ _ _ HCSc SCS) as SCSc;
      pose proof OPP as CRP; apply aobj_crange in CRP; pose proof OCUR as CRC; apply aobj_crange in CRC;
      pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 128 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP;
      pose proof (frame_apart_obj R HIA LB LF lo _ CUR 64 FB 128 FRSH CWC ltac:(clear; lia) ltac:(clear; lia) LOS) as APC;
      pose proof FRSH as FRSH'; unfold fresh_apart in FRSH'; destruct FRSH' as (F0 & F1 & F2 & F3);
      pose proof (F3 BUF n ltac:(apply in_or_app; left; exact BIN)) as APB;
      pose proof (art_stk_high asegs R HIA) as STKH;
      assert (INF : In (FB, 128) ((FB, 128) :: LF)) by (left; reflexivity);
      pose proof (hm_fresh_frame_apart asegs R HIA hc Lh LF mc FB 128 HHc) as AP;
      assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]);
      assert (WCC : wcover R LB LF (bv_unsigned sp) X0 CUR 64) by (apply wcover_inside; cbn [inside]; right; left; clear; lia);
      assert (WCP : wcover R LB LF (bv_unsigned sp) X0 PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia);
      assert (CWCc : client_wrange L (Lh ++ fdata ((FB, 128) :: LF)) lo (htop asegs R HIA hc) CUR 64)
        by (rewrite HTc; eapply client_wrange_mono; [exact CWC|]; intros b Hb; apply in_app_iff in Hb; apply in_app_iff;
            destruct Hb as [Hb|Hb]; [left; apply SUBL; exact Hb| right; apply (fdata_cons_sub b [] FB 128 LF); exact Hb]);
      assert (CWPc : client_wrange L (Lh ++ fdata ((FB, 128) :: LF)) lo (htop asegs R HIA hc) PP 8)
        by (rewrite HTc; eapply client_wrange_mono; [exact CWP|]; intros b Hb; apply in_app_iff in Hb; apply in_app_iff;
            destruct Hb as [Hb|Hb]; [left; apply SUBL; exact Hb| right; apply (fdata_cons_sub b [] FB 128 LF); exact Hb])
    end.

  (* [comment removed for export] *)
  Ltac cur_prep :=
    lazymatch goal with HHc : HM _ _ _ ?hc ?Lh ((?FB, 128) :: LF) ?mc, HTc : htop _ _ _ ?hc = _, HFR : nfreshA ?FB ?nodes, HCF : curFA ?nodes ?cur, FRSH : fresh_apart R LB LF ?FB 128,
                        SUBN : forall x, In x ?nodes -> In (x, 64) ?Lh, CWCc : client_wrange _ _ _ _ CUR 64, WCC : wcover _ _ _ _ _ CUR 64,
                        OCc : aobj _ _ (hcs _ _ _ ?hc) ?mc ?cur 64 |- _ =>
      destruct (cur_facts R HIA h LB LF PP BUF CUR lo slo bs BIN ALC CUR0 CWC CURLO DCB D1 SLOS SLOL FB nodes cur FRSH HFR HCF) as (CAL & CPOS & CLO & CPP & CBF & CFBa & CCASE);
      pose proof OCc as CRcur; apply aobj_crange in CRcur;
      assert (CWcur : client_wrange L (Lh ++ fdata ((FB, 128) :: LF)) lo (htop asegs R HIA hc) cur 64)
        by (destruct CCASE as [->|(HIN & _)]; [exact CWCc| eapply client_wrange_block; [apply in_or_app; left; exact (SUBN _ HIN)| clear; lia| clear; lia]]);
      assert (WCcur : wcover R LB LF (bv_unsigned sp) X0 cur 64)
        by (destruct CCASE as [->|(_ & NF)]; [exact WCC| eapply wcover_fresh; [exact (nodeF_fresh R LB LF PP CUR FB cur NF)| clear; lia| clear; lia| pose proof (art_lo asegs R HIA) as ALOx; clear - SLO LOS ALOx; unfold A_x509_get_name_A.STKn in SLO; lia]])
    end.

  Ltac nvA_fin HK9 MFc MF9 :=
    lazymatch goal with |- ?g => lazymatch g with context [A_x509_get_name_C.nvA] => idtac end end;
    lazymatch goal with HTc : htop _ _ _ ?hc = _, HSc : hstkhi _ _ _ ?hc = _, HFc : hflag _ _ _ ?hc = _, HCSc : forall x, CS x -> hcs _ _ _ ?hc x,
                        HVc : havol _ _ _ ?hc <= _, HFRc : hfr _ _ _ ?hc <= _ |- _ =>
      split; [eassumption|]; split; [exact HK9|]; split; [eapply mo_frame_trans; [exact MFc| exact MF9]|];
      split; [exact HTc|]; split; [exact HSc|]; split; [exact HFc|]; split; [exact HCSc|]; split; [exact HVc|]; split; [exact HFRc|];
      split; [eassumption|];
      spine;
      first [ eassumption | reflexivity
            | match goal with |- ?g => idtac "NVA-FIN-LEFT:" g end ]
    end.


  (* [comment removed for export] *)
  Ltac nvA_rebuild Dn :=
    lazymatch goal with |- aevtA _ (KF _ _ _ ?hc ?mocx) _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with HHc : HM _ _ _ hc ?Lh ((?FB, 128) :: LF) mx, HCF : curFA ?nodes ?cur, HVc : havol _ _ _ hc <= _ + ?PHIx, HFRc : hfr _ _ _ hc <= _ + ?FFRx,
                        FHD : rw_cells _ mx ?FB [C8 ?w0; C8 ?w1; C8 ?w2], GA : rw_cells _ mx (?FB + 32) [C8 ?ga], GB : rw_cells _ mx (?FB + 64) [C8 ?gb],
                        FSH : rw_cells _ mx (Z.shiftr ?FB 3 + _) [_; _; _; _; C1 ?b4; _; _; _; _; _; _; _; _; _; _; _],
                        RSL : rw_cells _ mx ?sp1 (CB 24 ?j0 :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: CB 16 ?j96 :: _),
                        HKc : HK _ _ _ hc mocx, MFc : mo_frame mo0 mocx |- _ =>
      assert (Dn : nvA FB sp1 w0 w1 w2 ga gb b4 j0 j96 Lh nodes cur PHIx FFRx mx mocx hc);
      [ nvA_fin HKc MFc (mo_frame_refl mocx) |]
    end end.

  (* [comment removed for export] *)
  Ltac start_W cur :=
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl (Wc cur) mx) as MU; unfold A_x509_get_name_C.Wc in MU; pose proof (wmono_refl asegs mx) as WM end.

  (* [comment removed for export] *)
  Ltac wsync :=
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with MU : munch _ ?mm mx, WM : wmono _ ?mm mx, HHD : headrep ?mm ?nodes, HLS : name_lseg _ ?mm ?Lh (removelast ?nodes) _,
                        HHc : HM _ _ _ ?hc ?Lh _ mx, HCF : curFA ?nodes ?cur, HFR : nfreshA ?FB ?nodes, HND : List.NoDup ?nodes,
                        SUBN : forall x, In x ?nodes -> In (x, 64) ?Lh |- _ =>
      let A := fresh "HHD" in let B := fresh "HLS" in
      pose proof (headrep_W R LB LF PP CUR D1 FB nodes cur mm mx HFR HCF HHD MU WM) as A;
      pose proof (lseg_W R HIA LB LF PP CUR FB Lh nodes cur hc ((FB, 128) :: LF) mx Lh mm mx (last nodes 0) HHc SUBN HND HFR HCF HLS MU WM) as B;
      clear HHD HLS MU WM; rename A into HHD; rename B into HLS
    end end.

  Local Notation InnerOb := (InnerOb R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PP P END BUF CUR lo slo d bs).
  Local Notation OuterOb := (OuterOb R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PP P END BUF CUR lo slo d bs).
  Local Notation zname := [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16); C8 (Z_to_bv 64 0);
                          CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)].

  Let err_exit' := err_exit R HIA IMG FREEL h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0
                     PP P END BUF CUR lo slo d bs LFB PP0 CWP PPLO BIN B1 B2 B3 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH TPV.
  Let ok_exit' := ok_exit R HIA IMG h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0
                     PP P END BUF CUR lo slo d bs LFB PP0 CWP PPLO BIN B1 B2 B3 DPB CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH.

  (* [comment removed for export] *)
  Definition Wf (cur FB : Z) : list ivl := [(PP, PP + 8); (cur, cur + 64); (Z.shiftr FB 3 + al_sb AL, Z.shiftr FB 3 + al_sb AL + 16)].

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L38948636245.0L39188636933.0L40228640085.0L8520806293.12000001002003009SSSS1R2FB". (* [comment removed for export] *)
  #[using="Type"] Lemma node_apart_fsh : forall (hc : HST asegs R HIA) Lh LF' mq FB y,
    HM asegs R HIA hc Lh LF' mq -> In (y, 64) Lh -> crange (hcs asegs R HIA hc) FB 128 ->
    Z.shiftr FB 3 + al_sb AL + 16 <= y \/ y + 64 <= Z.shiftr FB 3 + al_sb AL.
  Proof.
    clear. intros hc Lh LF' mq FB y HH HIN CFBc.
    pose proof (hcs_block asegs R HIA hc Lh LF' mq y 64 HH HIN) as CRy.
    assert (SH : Z.shiftr FB 3 + al_sb AL = shadow_of AL FB) by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; lia).
    rewrite SH. eapply (apart_shadow_client AL (hcs asegs R HIA hc) y 64 FB _ 16); [exact (hcs_ok asegs R HIA hc)| exact CRy| exact CFBc| reflexivity| clear; lia| clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L38948636245.0L39188636933.0L8506124171.9 000001002008SSS1R2FB". (* [comment removed for export] *)
  #[using="Type"] Lemma client_apart_fsh : forall (hc : HST asegs R HIA) FB y k,
    crange (hcs asegs R HIA hc) y k -> 0 < k -> crange (hcs asegs R HIA hc) FB 128 ->
    Z.shiftr FB 3 + al_sb AL + 16 <= y \/ y + k <= Z.shiftr FB 3 + al_sb AL.
  Proof.
    clear. intros hc FB y k CRy Hk CFBc.
    assert (SH : Z.shiftr FB 3 + al_sb AL = shadow_of AL FB) by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; lia).
    rewrite SH. eapply (apart_shadow_client AL (hcs asegs R HIA hc) y k FB _ 16); [exact (hcs_ok asegs R HIA hc)| exact CRy| exact CFBc| reflexivity| exact Hk| clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L24091242290.3300000OS1R2PP2FB3cur1y2cs3Hsz2YP2YC2YS". (* [comment removed for export] *)
  #[using="Type"] Lemma lseg_Wf : forall FB Lh nodes cur (hc : HST asegs R HIA) mq LBn mm m1 fin,
    HM asegs R HIA hc Lh ((FB, 128) :: LF) mq -> (forall x, In x nodes -> In (x, 64) Lh) ->
    List.NoDup nodes -> nfreshA FB nodes -> curFA nodes cur -> crange (hcs asegs R HIA hc) FB 128 ->
    name_lseg asegs mm LBn (removelast nodes) fin ->
    munch (Wf cur FB) mm m1 -> wmono asegs mm m1 ->
    name_lseg asegs m1 LBn (removelast nodes) fin.
  Proof.
    clear. intros FB Lh nodes cur hc mq LBn mm m1 fin HH SUBN HND HFR HCF CFBc HL MU WM.
    eapply name_lseg_mem; [exact HL| intros y Hy; eapply name_lseg_in; [exact HL| exact Hy] |].
    intros y cs Hy HR Hsz. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. rewrite Hsz.
    ddestruct (others_apart R HIA LB LF PP CUR FB Lh nodes cur hc ((FB, 128) :: LF) mq y HH SUBN HND HFR HCF Hy) as ((_ & _ & _ & _ & _ & YP & _ & _) & YC).
    pose proof (node_apart_fsh hc Lh ((FB, 128) :: LF) mq FB y HH (SUBN _ (in_removelast _ _ Hy)) CFBc) as YS.
    cbn [disjoint_from Wf]. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L40228640085.0 L68048498031.2400000100OSS1R2PP3CUR2D12FB5nodes3NCU3CS'". (* [comment removed for export] *)
  #[using="D1"] Lemma headrep_Wf : forall FB nodes cur (hc : HST asegs R HIA) mm m1,
    nfreshA FB nodes -> curFA nodes cur -> crange (hcs asegs R HIA hc) CUR 64 -> crange (hcs asegs R HIA hc) FB 128 ->
    headrep mm nodes -> munch (Wf cur FB) mm m1 -> wmono asegs mm m1 -> headrep m1 nodes.
  Proof.
    clear - D1. intros FB nodes cur hc mm m1 HFR HCF CRC CFBc [->|(j & g & p7 & HR)] MU WM; [left; reflexivity|].
    destruct HCF as [[-> _]|(Hne & ->)]; [left; reflexivity| right].
    pose proof (HFR _ (last_in nodes Hne)) as (_ & _ & _ & _ & _ & _ & NCU & _).
    pose proof (client_apart_fsh hc FB CUR 64 CRC ltac:(clear; lia) CFBc) as CS'.
    dexists j, g, p7. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. cbn. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac start_Wf cur FB :=
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl (Wf cur FB) mx) as MU; unfold Wf in MU; pose proof (wmono_refl asegs mx) as WM end.

  (* [comment removed for export] *)
  Ltac wsyncf :=
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with MU : munch _ ?mm mx, WM : wmono _ ?mm mx, HHD : headrep ?mm ?nodes, HLS : name_lseg _ ?mm ?Lh (removelast ?nodes) _,
                        HHc : HM _ _ _ ?hc ?Lh ((?FB, 128) :: LF) mx, HCF : curFA ?nodes ?cur, HFR : nfreshA ?FB ?nodes, HND : List.NoDup ?nodes,
                        SUBN : forall x, In x ?nodes -> In (x, 64) ?Lh, CFBc : crange (hcs _ _ _ ?hc) ?FB 128, CRC : crange (hcs _ _ _ ?hc) CUR 64 |- _ =>
      let A := fresh "HHD" in let B := fresh "HLS" in
      pose proof (headrep_Wf FB nodes cur hc mm mx HFR HCF CRC CFBc HHD MU WM) as A;
      pose proof (lseg_Wf FB Lh nodes cur hc mx Lh mm mx (last nodes 0) HHc SUBN HND HFR HCF CFBc HLS MU WM) as B;
      clear HHD HLS MU WM; rename A into HHD; rename B into HLS
    end end.

  Let alloc_inner' := alloc_inner R HIA IMG CALLOC FREEL h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PP P END BUF CUR lo slo d bs
                        LFB PP0 CWP PPLO BIN B1 B2 B3 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV.
  Let alloc_outer' := alloc_outer R HIA IMG CALLOC FREEL h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PP P END BUF CUR lo slo d bs
                        LFB PP0 CWP PPLO BIN B1 B2 B3 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV.

  (* [comment removed for export] *)
  Ltac mk_blob W0 W1 W2 W3 W4 HCB :=
    let H1 := fresh "J" in let H2 := fresh "J" in let H3 := fresh "J" in
    chunk_join W3 W4 H1; chunk_join W2 H1 H2; chunk_join W1 H2 H3; chunk_join W0 H3 HCB;
    lazymatch type of HCB with rw_cells ?sg ?mx ?A ?cs =>
      let n := eval cbv in (length cs - 3)%nat in
      let mid := eval cbv beta iota delta [firstn] in (firstn n cs) in
      let post := eval cbv beta iota delta [skipn] in (skipn n cs) in
      change (rw_cells sg mx A cs) with (rw_cells sg mx A ([] ++ mid ++ post)) in HCB;
      apply (rw_cells_merge sg mx A [] mid post) in HCB;
      cbn [cells_size csize Nat.add app] in HCB;
      change (CB 48 ?j :: ?rest) with (name_blob j 0) in HCB || idtac
    end.

  (* [comment removed for export] *)
  Ltac go_err W0 W1 W2 W3 W4 keep :=
    let HCB := fresh "HCB" in let D3 := fresh "D3" in
    mk_blob W0 W1 W2 W3 W4 HCB; nvA_rebuild D3;
    intros moq [HKq MFq];
    eapply err_exit';
      first [ eapply nvA_mo; [exact D3| exact HKq| exact MFq] | exact HCB | eassumption
            | lazymatch goal with
              | |- P <= _ <= END => keep; lia
              | |- _ + _ * AVOL_CALL <= _ => unfold A_x509_get_name_A.PHIn; unfold AVOL_CALL in *; keep; nia
              | |- _ + _ * fr_charge 0 <= _ => unfold A_x509_get_name_A.FFRn; keep; pose proof (Z.le_max_r 0 (fr_charge (d + 1))); pose proof (Z.le_max_l 0 (fr_charge (d + 1))); unfold fr_charge in *; nia
              | |- - 12288 < _ < 0 => first [clear; lia | keep; lia]
              end
            | match goal with |- ?g => idtac "GOERR-LEFT:" g end ].

  Let l3_walk' := l3_walk R HIA IMG CALLOC FREEL h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PP P END BUF CUR lo slo d bs
                    LFB ALP PP0 CWP PPLO HBY BIN B1 B2 B3 B47 B5 B30 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV.

  (* [comment removed for export] *)
  Definition Ws (cur sp1 : Z) : list ivl := [(PP, PP + 8); (cur, cur + 64); (lo, sp1)].

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L24091240226.3800000fS1R2PP2lo3slo4SLOS4SLOL3sp13cur3ALO1y2cs3Hsz3YCE2YP2YC". (* [comment removed for export] *)
  #[using="slo SLOS SLOL"] Lemma lseg_Ws : forall FB sp1 Lh nodes cur (hc : HST asegs R HIA) mq LBn mm m1 fin,
    HM asegs R HIA hc Lh ((FB, 128) :: LF) mq -> (forall x, In x nodes -> In (x, 64) Lh) ->
    List.NoDup nodes -> nfreshA FB nodes -> curFA nodes cur ->
    name_lseg asegs mm LBn (removelast nodes) fin ->
    munch (Ws cur sp1) mm m1 -> wmono asegs mm m1 ->
    name_lseg asegs m1 LBn (removelast nodes) fin.
  Proof.
    clear - SLOS SLOL. intros FB sp1 Lh nodes cur hc mq LBn mm m1 fin HH SUBN HND HFR HCF HL MU WM.
    pose proof (art_lo asegs R HIA) as ALO.
    eapply name_lseg_mem; [exact HL| intros y Hy; eapply name_lseg_in; [exact HL| exact Hy] |].
    intros y cs Hy HR Hsz. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. rewrite Hsz.
    ddestruct (others_apart R HIA LB LF PP CUR FB Lh nodes cur hc ((FB, 128) :: LF) mq y HH SUBN HND HFR HCF Hy) as ((_ & _ & YCE & _ & _ & YP & _ & _) & YC).
    cbn [disjoint_from Ws]. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L68048577873.2200000RS2PP3CUR2lo5CURLO2D13sp15nodes3NCU". (* [comment removed for export] *)
  #[using="CURLO D1"] Lemma headrep_Ws : forall FB sp1 nodes cur mm m1,
    nfreshA FB nodes -> curFA nodes cur ->
    headrep mm nodes -> munch (Ws cur sp1) mm m1 -> wmono asegs mm m1 -> headrep m1 nodes.
  Proof.
    clear - D1 CURLO. intros FB sp1 nodes cur mm m1 HFR HCF [->|(j & g & p7 & HR)] MU WM; [left; reflexivity|].
    destruct HCF as [[-> _]|(Hne & ->)]; [left; reflexivity| right].
    pose proof (HFR _ (last_in nodes Hne)) as (_ & _ & _ & _ & _ & _ & NCU & _).
    dexists j, g, p7. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. cbn. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac start_Ws cur sp1 :=
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl (Ws cur sp1) mx) as MU; unfold Ws in MU; pose proof (wmono_refl asegs mx) as WM end.

  (* [comment removed for export] *)
  Ltac wsyncs :=
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with MU : munch [_; _; (lo, ?sp1)] ?mm mx, WM : wmono _ ?mm mx, HHD : headrep ?mm ?nodes, HLS : name_lseg _ ?mm ?Lh (removelast ?nodes) _,
                        HHc : HM _ _ _ ?hc ?Lh _ mx, HCF : curFA ?nodes ?cur, HFR : nfreshA ?FB ?nodes, HND : List.NoDup ?nodes,
                        SUBN : forall x, In x ?nodes -> In (x, 64) ?Lh |- _ =>
      let A := fresh "HHD" in let B := fresh "HLS" in
      pose proof (headrep_Ws FB sp1 nodes cur mm mx HFR HCF HHD MU WM) as A;
      pose proof (lseg_Ws FB sp1 Lh nodes cur hc mx Lh mm mx (last nodes 0) HHc SUBN HND HFR HCF HLS MU WM) as B;
      clear HHD HLS MU WM; rename A into HHD; rename B into HLS
    end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "09n0@C40858145355.279C7804676499.278 D10636937134.279D12781061969.256D16071854214.279D16901939902.279D28498761192.244D28498761192.252D35656734845.279D41869862308.243D43427672.279   D4451634193.244 D4451634193.252 D46794843979.279D60109196847.243D60109196847.244D60109196847.252D60109196847.256D60109446735.279D62376725824.243D62376725824.256K12226132804.243K12226132804.256K15835051771.243K15835051771.256K15958421307.244K15958421307.252K1932217360.278 K20337545906.277K20981739667.277K21870859916.243K21870859916.256K22945712379.243K22945712379.256K23672143632.279K2431698795.244 K2431698795.252 K28077304394.279K30993319891.279K3337916572.244 K3337916572.252 K34516387472.277K40598034112.277K41252654395.244K41252654395.252K44164039966.243K44164039966.244K44164039966.252K44164039966.256K4549514449.277 K48008378065.277K48539967931.244K48539967931.252K52094252219.244K52094252219.252K59810587792.278K64038415723.244K64038415723.252K65858155712.277K67298046963.277K9840090748.244 K9840090748.252 L11431517604.16 L11949961375.1  L12219316802.2  L12757185696.4  L13199423329.8  L14447267832.2  L14813823902.240L15487692983.236L15825090557.2  L15934535645.1  L15969431101.2  L16641873078.1  L16772002776.285L1685717371.0   L17523603370.285L179075641.248  L179075641.254  L1848725797.246 L1848725797.248 L1848725797.252 L1848725797.253 L1848725797.282 L19072738292.245L19078215335.1  L1942461814.2   L20246203949.1  L20348306388.2  L20923585658.2  L20977711877.2  L21055533038.245L21654730866.2  L21868238730.2  L22353701966.7  L22938896893.2  L23182876091.2  L23657246326.2  L24023900370.0  L2419170461.2   L2485050449.2   L2487147605.2   L25693330238.8  L2621559066.1   L26386499879.1  L26443884051.247L26443884051.249L26443884051.253L26443884051.254L26443884051.283L27111942217.1  L27286562470.8  L2784014976.3   L27897054220.3  L27940405558.8  L28074933036.3  L29010574176.233L29162521377.0  L29311754221.267L29313646868.265L29943930407.1  L30507144274.2  L3055355236.3   L30997223346.3  L31393302313.248L31393302313.250L31393302313.254L31393302313.255L31393302313.284L31789301242.2  L31936509856.236L31938607076.242L31939521696.238L33200185116.0  L3323761050.2   L34478438048.232L34522961910.2  L35139482716.0  L35497690860.3  L35497693828.3  L35499788008.3  L35627047303.1  L35662219547.1  L35666023782.10 L37156630869.0  L3755151578.2   L38235734261.1  L38236685598.4  L38383890888.1  L38695569825.10 L3930512633.232 L39332637397.0  L40038518010.28 L40228640085.0  L40585223510.2  L41202929119.232L41202929119.233L41202929119.241L41241644093.2  L42411609006.0  L43090580551.2  L44166661144.3  L44168742175.3  L45567083625.231L4559259063.2   L46439757434.245L47870616696.2  L47899738467.2  L48006522807.2  L48117785831.9  L48550977725.2  L49478371288.2  L49869479980.2  L50678314462.3  L50925318027.2  L52108408253.2  L52516244784.241L52827750573.1  L52836338583.23 L5290740061.7   L52991222996.1  L53271535775.233L53271535775.241L5401337660.3   L54261998223.2  L54935543197.24 L56464645271.1  L56465858132.28 L56473405084.246L56475621844.243L56694929206.249L56694929206.251L56694929206.255L56694929206.256L56694929206.285L57894927187.2  L58039649675.2  L58451383419.10 L58972524609.3  L59139600103.233L59308579414.10 L59442115284.232L59795174902.2  L60098763854.6  L60812373952.10 L61672228356.279L62508983033.233L62525477031.1  L63693465645.1  L64009471222.1  L64025917085.2  L64148832490.251L64148832490.257L64148832490.258L64179129035.1  L64370849402.2  L64517051825.240L65055730314.1  L65313839333.23 L65320797075.1  L65862516566.2  L66151426447.10 L66151427842.16 L66298372189.2  L66812728480.3  L67070089790.2  L67304579733.2  L68226020255.232L68519772063.1  L7735485449.2   L8171953640.251 L8171953640.257 L8171953640.258 L8175984452.232 L8176057100.237 L8176057100.243 L8178151109.234 L881835912.0    L9080220944.4   L9356559676.15  L9748633241.2   L9835808138.2   N13467909276.278N7984367253.278 N9227617910.278 N9984517160.278 O10644243082.277O10871149737.276O12822076515.277O14075571866.278O14632083704.277O14912726833.277O16962713170.279O17217116232.277O18988691132.277O21298244344.278O22525005962.277O24222861850.278O3068598504.277 O32831042147.277O32835402212.277O33449646875.277O33496826488.279O3493317847.277 O37559489567.279O3821773283.279 O39497886222.276O44938202843.277O4776649498.279 O50011839873.277O54119978487.277O55188689906.277O55209884805.277O56134767679.277O58364443802.277O64474006218.277O65961212488.277P14461423358.243P14461423358.256P20934313244.277P23170010975.244P23170010975.252P2770101222.276 P30511339222.277P3069564867.276 P31778598044.279P38605639612.257P38605639612.263P38605639612.264P38605639612.291P47876372191.277P49872318794.277P50671478649.277P50927926572.277P51370907562.257P51370907562.263P51370907562.264P51370907562.291P53346601986.257P53346601986.263P53346601986.264P53346601986.291P5387390554.277 P54268551240.244P54268551240.252P57883666997.277P58041177900.277P64359622428.278P66292560634.277P66818508295.279P66903681610.257P66903681610.263P66903681610.264P66903681610.291P67064334489.277P7740881908.257 P7740881908.263 P7740881908.264 P7740881908.291 P7750690063.243 P7750690063.256 P9764112383.277 Q10636937134.279Q10646134994.279Q10649498890.240Q10649498890.249Q10649537205.239Q10651698952.248Q10821824020.257Q10821824020.263Q10821824020.264Q10821824020.291Q12462889934.248Q12462889935.247Q12464982158.241Q12464986477.241Q12465444467.275Q12658605510.257Q12658605510.259Q12658605510.263Q12658605510.264Q12658605510.265Q12658605510.266Q12658605510.291Q12658605510.293Q12781061969.256Q12783013201.255Q13733092405.248Q13734859144.239Q13846928860.279Q13851160440.240Q13851160440.249Q15902025364.241Q15930096381.245Q15930096381.251Q16429527224.279Q16795010073.245Q16795010073.251Q16795010073.252Q16796962909.247Q16807452132.280Q17027695041.279Q17681074618.279Q17701933584.240Q17701933584.249Q17841111261.254Q17841111261.260Q17841111261.261Q17841111261.288Q19791518367.251Q21203241386.245Q21203241386.251Q21203241386.253Q21204913491.247Q21269723930.245Q21269723930.251Q21269723930.253Q21271461859.247Q21767670690.279Q21915195062.247Q21915195063.248Q24054947262.240Q2613652986.245 Q2613652986.251 Q2613652986.253 Q2616174851.247 Q26295627581.254Q27573751300.279Q27942454161.279Q2803826605.279 Q2819779634.248 Q2819927268.242 Q28496781288.243Q28496781288.251Q28498761192.244Q28498761192.252Q29471257687.239Q29775981542.279Q30263103398.240Q3054610265.247 Q3056825117.245 Q3056825117.251 Q3056825117.252 Q3067389030.239 Q3067468761.240 Q3069291232.280 Q31524949867.252Q31526414380.257Q31526414380.263Q31526414380.264Q31526414380.291Q3215835802.252 Q3215835802.258 Q3215835802.259 Q3215835802.286 Q32681607669.279Q33137450695.279Q33283861378.257Q33283861378.263Q33283861378.264Q33283861378.291Q33342515655.253Q34357517856.251Q34357517856.257Q34357517856.258Q34357517856.285Q34390149656.240Q34390149656.249Q34669208222.252Q34669208222.258Q34669208222.259Q34669208222.286Q34964695579.250Q34964695579.256Q34964695579.257Q34964695579.284Q35656455769.247Q35656455769.253Q35656455769.254Q35656734845.279Q35658433053.279Q35662748640.246Q36719006557.240Q36915773936.245Q36915773936.251Q36915773936.253Q36918035721.247Q36986196939.245Q36986196939.251Q37216054521.241Q37216054521.249Q38053871235.239Q38372880008.249Q38372880008.255Q38372880008.256Q38372880008.283Q39600066516.240Q39600066516.249Q39721805318.245Q39721805318.251Q39721805318.253Q39723886648.242Q39723999999.247Q39724034286.248Q40354196046.257Q40354196046.263Q40354196046.264Q40354196046.291Q40360481330.242Q40360481330.248Q40360481330.249Q40360481330.276Q41261939883.248Q41675861917.245Q41677880281.281Q41688364640.246Q41688364640.252Q41688364640.253Q41867653028.242Q41869862308.243Q42222684417.254Q42377995046.241Q42389460319.279Q42439168719.279Q42439443119.243Q42439443119.244Q42439443119.252Q42439443119.256Q42441548847.257Q42441548847.263Q42441548847.264Q42441548847.291Q42887926878.248Q42887926878.254Q42887926878.255Q42887926878.282Q42892372189.241Q43138029699.257Q43138029699.263Q43138029699.264Q43138029699.291Q43427672.279   Q43479930840.279Q43610413609.242Q43610594047.248Q44298944140.242Q44298944140.248Q44298944140.249Q44298944140.276Q44301027056.257Q44301027056.263Q44301027056.264Q44301027056.291Q4451634193.244 Q4451634193.252 Q4453582353.243 Q4453582353.251 Q45482765142.259Q45482765142.265Q45482765142.266Q45482765142.293Q45883722421.254Q46794843979.279Q47799518061.241Q47799521934.241Q47799716979.275Q47801614798.248Q47801614799.247Q48119910507.257Q48119910507.263Q48119910507.264Q48119910507.291Q49698585326.241Q49698585326.254Q50458135125.254Q52817561962.240Q53369276613.247Q53370948668.245Q53370948668.251Q53370948668.253Q54481541668.251Q54481541668.257Q54481541668.258Q54481541668.285Q5596578838.257 Q5596578838.263 Q5596578838.264 Q5596578838.291 Q56204695986.279Q59865321072.243Q59865321072.244Q59865321072.252Q59865321072.256Q59865603600.279Q59867425008.257Q59867425008.263Q59867425008.264Q59867425008.291Q61556549392.242Q61556549392.250Q61847600945.240Q61847600945.249Q61908763639.244Q61908763639.252Q62374774592.242Q62374774592.255Q62376725824.243Q62376725824.256Q63720980196.246Q63720980196.252Q63720980196.253Q63733638937.245Q63735657309.281Q64228675114.256Q64228675114.262Q64228675114.263Q64228675114.290Q64650680438.249Q64650680438.255Q64650680438.256Q64650680438.283Q64681563910.257Q64681563910.263Q64681563910.264Q64681563910.291Q64683667846.243Q64683667846.244Q64683667846.252Q64683667846.256Q64683942374.279Q65752674778.248Q65752674778.254Q65752674778.255Q65752674778.282Q65765526873.241Q65765575771.240Q6585298697.245 Q6585298697.251 Q6585298697.253 Q6587493360.247 Q67148156169.241Q68058681330.247Q68060678923.253Q68519243108.246Q68531942553.279Q68533919965.247Q68533919965.253Q68533919965.254Q6863764061.250 Q6863764061.256 Q6863764061.257 Q6863764061.284 Q6912043747.254 Q6912043747.260 Q6912043747.261 Q6912043747.288 Q7368703798.248 Q7528656170.248 Q7528656171.247 Q801816838.240  Q8223186191.245 Q8223186191.251 Q8945570072.251 Q9077888740.254 Q9079820891.251 Q9080277594.252 Q9356757767.256 Q9485152634.257 Q9485152634.263 Q9485152634.264 Q9485152634.291 Q9487243258.243 Q9487243258.244 Q9487243258.252 Q9487243258.256 Q9516151461.245 Q9516151461.251 Q9644583048.279 00000400900g01g04>05^06c07h08V09V0:D0;I0<N0=<0>C0?O0@[0Ab0BW0CW0DW0ET0FQ0GR0HS0IU0JW0Kl0ME0N]0O^0P_0Q`0Ra0T60U70V80WQ0X<0Y>0Z@0[U0\m0]o0_10`20a40b60c70dP0ei0fk0gm0ho0j10kF0lG0mH0n`10511612712_12d12e13513Q13R13S15J15K15N15O15T15U15V16e17_18Y19G1:51:c1;Q1<?1<@1<E1<F1<K1<L1<M1<N1=<1==1=>1=W1=X1=Y1=Z1=[1=\1=]1=^1>;1>@1>E1?31?a1@O1A=1Ak1Ao1BK1BL1BX1Bm1Bn1Bo1C01C11C21C31C41C51C61Cd1DR1E@1En1F\1F]1Hi1K51MA1MB1MC1Ol1Om1On1Oo1P01P11P81P=1PS1PT1P^1Pb1Q21Q71QT1RB1RC1S;1S<1S=1Sk1TY1UG1UH1UI1UO1UP1UQ1Vk1Vl1WZ1W[1Wc1Wd1XD1XE1XM1XN1XO1XP1XQ1Y?1YD1Z11ZL1ZQ1[?1[m1[n1[o1\d1\e1]51^O1_i1`W1aE1b31ba1cO1cP1cQ1cc1co1f;1fR1gl1gm1h71hT1hU1iC1iH1iM1iN1iO1j]1kk1m91m:1m;1mi1mn1n<1n=1n>1nN1o21o31o41o51o61od1oi1oj1ok1ol1om22V25?27h2:Q2:R2:a2;F2;G2;H2=M2>:2>g2?T2?U2?V2?W2?X2?Y2?Z2?[2?\2?]2?^2?_2?`2?a2?b2?c2?d2?e2?f2?g2?h2?i2?j2?k2?l2?m2?n2AA2AB2AC2AD2AE2CS2El2H32J=2LC2MM2OT2Qc2Sj2U22V52W82X;2YK2[R2\A2]Q2^Z2_^2`b2af2d>2eY2g42hO2iA2kS2ma2nc31033733b35B36F37E38D39C3;R3<V3=U3>T3?S3@g3B;3DB3De3Df3EI3El3FO3G23H13I03Io3Jn3KT3L:3L`3MF3Ml3Nk3P<3Q;3R:3SK3T\3U[3W03Wi3Xb3YE3Yh3Yi3Yj3Yk3[n3\Q3]43^>3_73`03`i3ab3b[3c>3eM3f03fS3gH3h=3i23ig3jN3jO3jP3jQ3jR3jS3jT3jU3jV3l]3n\40[41B41C41D41E41F41i41j43i44P45o47N48H49B4:<4;64;]4<H4=f4>_4?X4@Q4AJ4B14BX4CQ4D84D94D:4D;4D<4E14Ef4F[4GP4GQ4H?4H@4HA4HB4HC4I24Ij4Jb4KZ4LR4LS4LT4MI4N>4O34Oh4RA4TR4Vc4Y44Ym4Zf4[_4\F4]?4^84^_4^`4^a4^b4^c4`A4a_4bI4c34cZ4dS4eL4fE4g>4g?4g@4i04j`4lP4n@50051`52[53V54Q55L56556^57G58058^59W5:P5;I5<B5=;5>45>m5?T5A25AY5BE5CG5DJ5EM5FO5GS5HW5I[5J_5KX5LQ5MJ5NC5Nj5Nk5Nl5Nm5Nn5OU5Qd5RG5Rj5SS5T<5Te5UN5VI5WD5X?5Y:5Z45Zn5[h5\b5^35_D5`U5aj5bV5c95c_5dE5dk5eQ5f75hN5ih5kB5l\5mL5n<5nc5oJ5oK5oL5oM5oN61W62c63o65;65<65=65>65?65@65A65B65C65D65E65F65G65H65I66566a67f68k68l68m69f6:_6;X6<Q6=J6>C6?<6@56@n6CO6EB6G56IY6JR6KK6LD6M=6O^6R76TP6Vi6Y56[B6]R6_i6aj6bc6c\6dU6eN6f56f\6f]6f^6f_6f`6gN6hm6jL6kE6l>6m76n06ni6oi70i71i72i73^74S75H76=77?77m78[79J7:i7<H7<k7=R7>97>`7?L7@K7AJ7BI7CH7DD7EE7FF7GB7Gm7HX7IAS2PPS3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2tb3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS2FB3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB3KO0S1R3HIA1h2LF2sp2PP1P3END3CUR1d2bs3LFB3PP02B24CUR03TOP2FB3sp13cur2hc3HTc3SP13SPR2F04CPOS4SP1R3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13cur2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13cur4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13cur4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13cur2tb3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2tb3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2tb3CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2q24CFBa3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2tb4CFBa3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur4olen2e22q23x143CPP3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur4olen2e22q23x144CFBa3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur4olen2e22q23x143APP3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2q24CFBa3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2tb4CFBa3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2q24CFBa3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2tb4CFBa3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur4olen2e22q23x143CPP3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB4olen2q23APP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB4olen2q23APP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3sp13cur4olen2e22q23x143CBF3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3DPB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur4olen2e22q23x143CPP3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur4olen2e22q23x143APP3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3cur2q23CBF3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3DPB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3DPB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3cur2tb3CBF3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur4olen2e22q23x144CFBa3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur4olen2e22q23x144CFBa3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur4olen2e22q23x143CPP3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB4olen2q23APP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB4olen2q23APP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur4olen2e22q23x143APP3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur4olen2e22q23x143CPP3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB4olen2q23APP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB4olen2q23APP3PPB2HB5Ha_st5Hl_stS1R2sp3BUF2lo2bs3SLO3LOS3sp13SP13ALO3BCES3CURFS3BUF2bs3cur3CBFS1P3END2p02e22es3Hp03He23HesFFS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B22B33DPB4CUR03DCB2D12FB3sp13cur4olen2e22es2q23He23Hes3SPR2F04CPOS4SP1R3PPB3KO0FS1lFS3curFSS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPB2HB5Ha_st5Hl_st5SAEst5CM8st2x22HxS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3sp13cur4olen2q23PPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3sp13cur4olen2q23PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBFS3curFS3curFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBFFS1P3BUF2B14olen2q23Hq12LRFFFSFSSS3END3BUF2bs2B32e22es3He23HesS3sp1S3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS2PPS1P4olen2e22q23Hq12LR2q33Hq3FS2PP3cur3CPPS1R2sp2lo3SLO3sp13SP1FFSFFFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBFS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13cur4olen2p02e22es2q23Hq13He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13cur4olen2p02e22es2q23Hq13He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13cur4olen2p02e22es2q23Hq13He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB3KO0SFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B472B53DPB4CUR05CURLO3DCB2D13SLO3SPH2FB3sp13cur4olen2p02e22es2q23Hq23HOL3He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPBFSSSSS5nodesS3curS1R3HIA1h2sp2lo3TOP2HTSS3cur4CPOSS2loS4olen2e22q23KO0S3curS1R2sp2lo3SLO3sp13cur3SP13CLOS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBSS1P3END1d4olen2p02e22es2q23Hq13Hp03He23Hes3HP02LR2q33Hq3SFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBFSS1r2HrFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3SPH2FB3sp13cur3SPR2F04CPOS3CLO4SP1R3PPBFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBFS2rv3HrvFS1R2sp2lo3slo4SLOS4SLOL3SLO4ALOxFS2sp3sp1FFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS3curS1P3END1d2p02e22es2q23Hq13Hq23Hp03He23Hes3HP0S4olen2p02q23HK42LR2q34Hq3aS3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBFFS1P3END1d4olen2p02e22es2q23Hq13HOL3Hp03He23Hes3HP02LRFS1P3END1d2rv3HrvS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3SPH2FB3sp13cur3SPR2F04CPOS3CLO4SP1R3PPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3SPH2FB3sp13cur3SPR2F04CPOS3CLO4SP1R3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBFFS2rv3Hrv1r3Krv1q1HS3BUF2bs3B47S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D12FB3sp13cur4olen2p02e22es2q23HOL3He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPBS1r2Hr2r02KZ1q1H2rv3HrvS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3SPH2FB3sp13cur3SPR2F04CPOS3CLO4SP1R3PPBFS1R2lo3LOSS1R2sp2PP2lo4PPLO3SLO3sp13SP1FS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS3curS3curFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPB2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPB2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPB2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS3curS1P3END1d1r2HrFFS1r2Hr2r02Kr1q1HS3cur2r03CAL1q1r1H2H02q02H43sp14SP1MFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS3curFFFFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B472B53DPB4CUR05CURLO3DCB2D13SLO3SPH2FB3sp13cur4olen2p02e22es2q23Hq13HOL3He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B472B53DPB4CUR05CURLO3DCB2D13SLO3SPH2FB3sp13cur4olen2p02e22es2q23Hq13He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B472B53DPB4CUR05CURLO3DCB2D13SLO3SPH2FB3sp13cur4olen2p02e22es2q23Hq13He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B472B53DPB4CUR05CURLO3DCB2D13SLO3SPH2FB3sp13cur4olen2p02e22es2q23Hq13He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB3KO0SS2sp2lo3sp13SP1S1R2sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO03x181CS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPB3x181CS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPB3x181CS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPB3x181CFFFFFFFFFFFFFFFFFFFFFFFFFFS1R2LF2sp2PP1P3END3BUF3CUR2lo2bs3LFB3PP02B12B22B33DPB4CUR05CURLO3DCB2D13SLO3sp13SP1FFFFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur2p02e22es2q23SP13Hq23He23Hes3HP03HK43SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur4olen2p02e22es2q23SP12tb3He23Hes3HP03HK43SPR3CLO2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR3CLO2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO4olen2p02e22es2q23Hq23HOL3He23Hes3HP03HK43SPR2LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO4olen2p02e22es2q23He23Hes3HP03HK43SPR2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLO3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS4olen2p02e22es2q23He23Hes3HP03HK43ALO3SPR2LR3PPB3KO03BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43ALO3SPR2LR3PPB3KO03BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR3CLO2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB1r2Hr3APB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3APB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3APB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3APB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F13PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR3CLO2LR3PPB3KO0S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB4PPLO3sp13PPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F13PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur1r2Hr4CFBa3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4CFBa3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4CFBa3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4CFBa3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB3PP02B24CUR04SLOS2FB3ALO3SPR2F13PPB2HB5Ha_st5Hl_st5SAEst3BUF2B12B33B303DPB3DCB2D14olen2p02e22es2q23He23Hes3HP03HK42LRS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB3PP02B24CUR04SLOS2FB3ALO3SPR2F13PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB3PP02B24CUR04SLOS2FB3ALO3SPR2F13PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB3PP02B24CUR04SLOS2FB3ALO3SPR2F13PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur3CLO3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO3sp14olen2p02e22es2q23SP13Hq23HOL3He23Hes3HP03HK43SPR2LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3cur3SPR3CLO3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS2FB3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43ALO3SPR2F12LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR3CLO2LR3PPB3KO0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP13PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B24CUR05CURLO2D13SLO3LOS3sp13SP13ALO3SPR3PPB3BCES1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB1r2Hr3APC3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APC3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APC3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APC3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43ALO3SPR2LR3PPB3KO03BCES1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB1r2Hr3APP3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APP3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APP3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APP3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3cur2q23SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3cur2tb3SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR3CLO2LR3PPB3KO0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB3BCE2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2tb3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2tb3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBFFFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3sp14olen2p02e22es2q23SP13Hq23He23Hes3HP03HK43SPR2LR3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLO3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43ALO3SPR2LR3PPB3KO03BCES1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBFFFFFFFFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43ALO3SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B22B33DPB4CUR03DCB2D14olen2e22es2q23He23Hes3SPR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B22B33DPB4CUR03DCB2D14olen2e22es2q23He23Hes3SPR3PPB3KO0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP13PPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3SPR2F03CAL4CPOS4SP1R3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP13PPBFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4CPOS3PPB2HBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2FB3sp12p02e22es3SP13Hp03He23Hes3HP03SPR3PPB2HB5Ha_st5Hl_st3B304olen2q23Hq23HK42LRS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2FB3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2FB3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2FB3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBFFFFS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B53DPB4CUR02D14olen2p02q23Hq13HP03HK43SPR2LR3PPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B53DPB4CUR02D14olen2p02q23Hq13HP03HK43SPR2LR3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PP03PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PP03PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stFFS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D14olen2p02e22es2q23He23Hes3HP03HK43SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D14olen2p02e22es2q23He23Hes3HP03HK43SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D14olen2p02e22es2q23He23Hes3HP03HK43SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D14olen2p02e22es2q23He23Hes3HP03HK43SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D14olen2p02e22es2q23He23Hes3HP03HK43SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D14olen2p02e22es2q23He23Hes3HP03HK43SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP13PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3SPR2F03CAL4CPOS4SP1R3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS3PPBS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS3cur2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS3cur2tb3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33DPB4CUR05CURLO3SLO3LOS3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43ALO3SPR2LR3PPB3KO03BCES1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB3BCE2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4CPOS3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3ALO3SPR3PPB2HB5Ha_st5Hl_st5SAEst3BUF2B12B33B303DPB3DCB2D14olen2p02e22es2q23He23Hes3HP03HK42LRS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3ALO3SPR3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3ALO3SPR3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3ALO3SPR3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPB2HB5Ha_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPB2HB5Ha_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBFFFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO2FB3SPR3PPB2HB5Ha_st5Hl_st3BUF2B12B33B303DPB3DCB2D14olen2p02e22es2q23He23Hes3HP03HK42LRS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO2FB3SPR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO2FB3SPR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO2FB3SPR3PPB2HB5Ha_st5Hl_stFFFFFFFFFFFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPB2HB5Ha_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPB2HB5Ha_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3ALP3PP02B22FB3sp13cur3SPR2F04SP1R3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3ALP3PP02B22FB3sp13cur3SPR2F04SP1R3PPBFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2tb3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2tb3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3F643SPR2F04CPOS4SP1R3PPB2HB5Ha_st5Hl_st5SAEst2B12B33B304olen2p02e22es2q23He23Hes3HP03HK42LRS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3F643SPR2F04CPOS4SP1R3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3F643SPR2F04CPOS4SP1R3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13cur4olen2p02e22es2q23F643He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB2q33Hq32HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP2FB2p02e22es3Hp03He23Hes3HP03SPR2HT3PPB2HB5Ha_st5Hl_st5SAEst3B304olen2q23Hq23HK42LRS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP2FB4olen2p02e22es2q23He23Hes3HP03HK43SPR2HT2LR3PPB3KO02HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP2FB4olen2p02e22es2q23He23Hes3HP03HK43SPR2HT2LR3PPB3KO02HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP2FB4olen2p02e22es2q23He23Hes3HP03HK43SPR2HT2LR3PPB3KO02HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP3cur2p02e22es2q23Hq23He23Hes3HP03HK43SPR2HT3PPB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP4olen2p02e22es2q23Hq23He23Hes3HP03HK43SPR2HT3PPB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP4olen2p02e22es2q23He23Hes3HP03HK43SPR2HT2LR3PPB3KO02HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP3cur4olen2p02e22es2q22tb3He23Hes3HP03HK43SPR2HT2LR3PPB3KO02HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP4olen2p02e22es2q23He23Hes3HP03HK43SPR2HT2LR3PPB3KO0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBFFFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP13PPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B22B33DPB4CUR03DCB2D14olen2e22es2q23He23Hes3SPR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B22B33DPB4CUR03DCB2D14olen2e22es2q23He23Hes3SPR3PPB3KO0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13SP13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13SP13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13SP13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13SP13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13SP13SPR3PPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP13PPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP13PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4CPOS3PPB2HBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B22B33DPB4CUR03DCB2D14olen2e22es2q23He23Hes3SPR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B22B33DPB4CUR03DCB2D14olen2e22es2q23He23Hes3SPR3PPB3KO0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp14SP1R3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2tb3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2F03PPB". (* [comment removed for export] *)
  #[using="IMG CALLOC FREEL LFB ALP PP0 CWP PPLO HBY BIN B1 B2 B3 B47 B5 B30 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS err_exit' l3_walk'"] Lemma l2_walk : forall FB sp1 w0 w1 w2 ga gb b4 j0 j96 nodes cur PHIx FFRx mc moc hc
      (otw : word) (r0 : list byte) (olen : word) (j1 : list byte) (vlen : word) (j2 : list byte) (mg' : byte) (p7 : list byte)
      (p0 e2 es q2 r : Z)
      (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    nvA FB sp1 w0 w1 w2 ga gb b4 j0 j96 (nLB nodes) nodes cur PHIx FFRx mc moc hc ->
    rw_cells asegs mc cur [C4 otw; CB 4 r0] -> rw_cells asegs mc (cur + 8) [C8 olen] ->
    rw_cells asegs mc (cur + 16) [CB 16 j1] ->
    rw_cells asegs mc (cur + 32) [C8 vlen] -> rw_cells asegs mc (cur + 40) [CB 8 j2; C8 (Z_to_bv 64 0); C1 mg'; CB 7 p7] ->
    rw_cells asegs mc PP [C8 (Z_to_bv 64 q2)] -> P <= q2 -> q2 <= e2 -> (r = 0 -> bv_unsigned olen <= e2 - q2) -> -0x7f < r <= 0 ->
    p0 < e2 -> e2 <= es -> es <= END -> P <= p0 ->
    6 * Z.of_nat (length nodes) <= p0 - P ->
    PHIx <= Z.of_nat (length nodes) * (2 * 64 + AVOL_CALL) -> FFRx <= Z.of_nat (length nodes) * Z.max 0 (fr_charge (d + 1)) ->
    havol asegs R HIA h + PHIn NB <= AVOL_MAX -> hfr asegs R HIA h + FFRn NB d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    (forall p' es', p0 < p' -> InnerOb p' es') -> (forall p', p0 < p' -> OuterOb p') ->
    (r = 0 -> p0 + 4 <= q2) ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 (-9088)) (Z_to_bv 64 PP) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
                      (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 cur) (Z_to_bv 64 es) (Z_to_bv 64 e2) (Z_to_bv 64 (cur + 8)) t3 t4 t5 t6)
                 F (Z_to_bv 64 0xac2cc) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until t6. intros D W0 W1 W2 W3 W4 PPc Hq1 Hq2 HOL Hr Hp0 He2 Hes HP0 CNT PHI FFR BUD BUDF UW KIN KOUT HK4. pose proof D as D0. nvA_open D. rt_facts. walk_prep. cur_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NRT; lia).
    assert (NN : 0 <= Z.of_nat (length nodes)) by (clear; lia).
    assert (KD : Z.of_nat (length nodes) <= NB / 6) by (apply (A_x509_get_name_A.cnt6_div _ (p0 - P)); [exact CNT| clear - Hp0 He2 Hes; lia]).
    pose proof (bv_unsigned_in_range 64 olen) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    pose proof (rw_cells_bound _ _ _ _ PPc) as PPB. cbn [cells_size csize Nat.add length] in PPB.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    start_Wf cur FB.
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr.
    { (* [comment removed for export] *)
      zstep. zstep.
      rewrite (swrap32_land_errsum r 18446744073709542528) by (clear - Hr; lia).
      zstep.
      zstep. if_cases KZ; zify_cond KZ.
      - wsyncf. go_err W0 W1 W2 W3 W4 ltac:(clear - PHI FFR CNT KD Hp0 He2 Hes HP0 NN Hq1 Hq2 Hr).
      - exfalso. clear - KZ Hr. change 18446744073709551615 with (Z.ones 64) in KZ. rewrite Z.land_ones in KZ by lia. Z.div_mod_to_equations. lia. }
    assert (R0 : r = 0) by (clear - Kr Hr; change 18446744073709551615 with (Z.ones 64) in Kr; rewrite Z.land_ones in Kr by lia; Z.div_mod_to_equations; lia).
    subst r. specialize (HOL eq_refl). specialize (HK4 eq_refl). clear Kr.
    (* [comment removed for export] *)
    do 9 zstep.
    (* [comment removed for export] *)
    do 8 zstep.
    (* [comment removed for export] *)
    zstep. if_cases KO; zify_cond KO.
    { (* [comment removed for export] *)
      zstep. zstep. zstep.
      wsyncf. go_err W0 W1 W2 W3 W4 ltac:(clear - PHI FFR CNT KD Hp0 He2 Hes HP0 NN Hq1 Hq2 LR HOL). }
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_chk OBUF (q2 + bv_unsigned olen) 1.
    get_byte bs (q2 + bv_unsigned olen - BUF) tb NBt. read_at BYc NBt (q2 + bv_unsigned olen - BUF) RDt.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. if_cases KT1; zify_cond KT1.
    { (* [comment removed for export] *)
      clear RDt. zstep. zstep. zstep. zstep.
      wsyncf. go_err W0 W1 W2 W3 W4 ltac:(clear - PHI FFR CNT KD Hp0 He2 Hes HP0 NN Hq1 Hq2 LR HOL). }
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. if_cases KT2; zify_cond KT2.
    { (* [comment removed for export] *)
      clear RDt. zstep. zstep. zstep. zstep.
      wsyncf. go_err W0 W1 W2 W3 W4 ltac:(clear - PHI FFR CNT KD Hp0 He2 Hes HP0 NN Hq1 Hq2 LR HOL). }
    (* [comment removed for export] *)
    clear RDt. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk OBUF (q2 + bv_unsigned olen) 1.
    (* [comment removed for export] *)
    read_at BYc NBt (q2 + bv_unsigned olen - BUF) RD2.
    zstep. zstep. zstep.
    shadow_chk OCc (cur + 24) 4.
    try clear RD2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    wsyncf.
    start_Ws cur sp1.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HH) as ABc end end.
    assert (OLEN : aobj asegs AL (hcs asegs R HIA hc) m1 (cur + 32) 8) by (eapply aobj_sub; [exact OCc| clear; lia| clear; lia]).
    pose proof (blocks_below_hm R HIA hc _ _ m1 _ HHc ltac:(intros b Hb; exact Hb)) as BBc.
    destruct (BBc (BUF, n) ltac:(apply SUBL; exact BIN)) as [_ BCE]. cbn [fst snd] in BCE. clear BBc.
    pose proof (A_asn1_get_len_spec AL IMG) as GL'. unfold asn1_get_len_stmtA, A_ASN1_GET_LEN in GL'.
    acallxA_sp sp1
      (eapply GL' with (CS := hcs asegs R HIA hc) (PP := PP) (LENP := cur + 32) (P := q2 + bv_unsigned olen + 1) (END := e2) (BUF := BUF) (bs := bs) (lo := lo) (lenv := vlen);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact PPc | exact W3 | exact BYc | exact OPP | exact OLEN | exact OBUF | exact CSOKc | exact ABc | exact (art_alwf asegs R HIA) | exact STlo | exact MIc
               | exact ALP | exact PP0 | exact B5 | exact DPB | reflexivity
               | lazymatch goal with
                 | |- BUF <= _ => clear - B1 Hq1 LR; lia
                 | |- _ <= e2 => clear - KO0; lia
                 | |- e2 <= BUF + _ => clear - He2 Hes B3; lia
                 | |- BUF + _ < 2 ^ 63 => clear - B47; lia
                 | |- PP + 8 <= cur + 32 \/ _ => clear - CPP; lia
                 | |- _ = 0 \/ PP + 8 <= BUF \/ _ => right; exact DPB
                 | |- _ = 0 \/ cur + 32 + 8 <= BUF \/ _ => right; clear - CBF; lia
                 | |- (cur + 32) mod 8 = 0 => clear - CAL; Z.div_mod_to_equations; lia
                 | |- 0 < cur + 32 => clear - CPOS; lia
                 | |- lo <= sp1 - 16 => clear - SLO SP1 NS1 NRT; unfold A_x509_get_name_A.STKn in SLO; lia
                 | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                 | |- crange _ lo _ => eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]
                 | |- PP + 8 <= sp1 - 16 \/ _ => left; clear - PPLO SLO SP1 NS1 NRT; unfold A_x509_get_name_A.STKn in SLO; lia
                 | |- cur + 32 + 8 <= sp1 - 16 \/ _ => left; clear - CLO SLO SP1 NS1 NRT; unfold A_x509_get_name_A.STKn in SLO; lia
                 | |- _ = 0 \/ BUF + _ <= sp1 - 16 \/ _ => right; left; clear - BCE ALO LOS SLO SP1 NS1 NRT; unfold A_x509_get_name_A.STKn in SLO; lia
                 end
               | match goal with |- ?g => idtac "GL-PRE-LEFT:" g end ]).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "GL-LEFT:" g end.
    clear GL' ABc OLEN.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rv end.
    match goal with H : _ < rv <= 0 |- _ => rename H into Hrv end.
    match goal with H : rv = 0 -> _ |- _ => rename H into HL0 end.
    match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into PPc; rename qq into q3 end.
    match goal with H : rw_cells _ _ (cur + 32) [C8 ?lw] |- _ => rename H into W3; rename lw into Lw end.
    match goal with H : _ <= q3 <= e2 |- _ => rename H into Hq3 end.
    wsyncs.
    (* [comment removed for export] *)
    zstep. if_cases Krv; zify_cond Krv.
    { (* [comment removed for export] *)
      assert (R0 : rv = 0) by (clear - Krv Hrv; change 18446744073709551615 with (Z.ones 64) in Krv; rewrite Z.land_ones in Krv by lia; Z.div_mod_to_equations; lia).
      subst rv. destruct (HL0 eq_refl) as [Hq3a HLw]. clear HL0 Krv.
      nvA_rebuild D3.
      intros moq [HKq MFq].
      eapply l3_walk' with (p0 := p0);
        first [ eapply nvA_mo; [exact D3| exact HKq| exact MFq] | exact W0 | exact W1 | exact W2 | exact W3 | exact W4 | exact PPc | exact HLw | exact Hp0 | exact He2 | exact Hes | exact HP0
              | exact CNT | exact PHI | exact FFR | exact BUD | exact BUDF | exact UW | exact KIN | exact KOUT
              | lazymatch goal with
                | |- P <= q3 => clear - Hq1 LR Hq3; lia
                | |- p0 + 6 <= q3 => clear - HK4 Hq3a LR; lia
                end
              | match goal with |- ?g => idtac "L2-L3-LEFT:" g end ]. }
    (* [comment removed for export] *)
    start_Wf cur FB.
    zstep. zstep.
    rewrite (swrap32_land_errsum rv 18446744073709542528) by (clear - Hrv; lia).
    zstep.
    zstep. if_cases KZ; zify_cond KZ.
    - wsyncf. go_err W0 W1 W2 W3 W4 ltac:(clear - PHI FFR CNT KD Hp0 He2 Hes HP0 NN Hq1 Hq2 LR HOL Hq3 Hrv).
    - exfalso. clear - KZ Hrv. change 18446744073709551615 with (Z.ones 64) in KZ. rewrite Z.land_ones in KZ by lia. Z.div_mod_to_equations. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
