(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_x509_get_name_A.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_len
     A_asn1_free_named_data_list_shallow A_crt_stmts A_crt_parse_stmts A_pkcs7_getcerts A_mpi_stmtA A_x509_get_name_stmt A_x509_get_name_stmtE A_x509_get_name_A A_x509_get_name_B A_x509_get_name_C A_x509_get_name_D A_x509_get_name_E A_x509_get_name_F A_x509_get_name_G.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0xad2bc]).
Local Ltac zchk_new ::= constr:([0xaccb0; 0xacd44; 0xacd48; 0xacd88; 0xacd8c; 0xacd90; 0xacdc0; 0xacdc4; 0xacdc8; 0xacdcc; 0xacdd0; 0xacdd4; 0xacdd8; 0xacdf4; 0xace00; 0xace1c; 0xace20; 0xace24; 0xace28; 0xace2c; 0xace40; 0xace48; 0xace4c; 0xace50; 0xace54; 0xace58; 0xace5c; 0xace60; 0xace64; 0xace68; 0xace6c; 0xace70; 0xace74; 0xace78; 0xace7c; 0xace80; 0xace84; 0xace88; 0xace8c; 0xace90; 0xace94; 0xace98; 0xace9c; 0xacea0; 0xacea4; 0xacea8; 0xaceac; 0xaceb0; 0xaceb4; 0xaceb8; 0xacebc; 0xacec0; 0xacec4; 0xacec8; 0xacecc; 0xaced0; 0xacee8; 0xacf18; 0xacf20; 0xacf24; 0xacf28; 0xacf2c; 0xacf30; 0xacf34; 0xacf38; 0xacf48; 0xacf7c; 0xacf80; 0xacf84; 0xacf88; 0xacfcc; 0xacfd0; 0xacfd4; 0xacfdc; 0xacff8; 0xacffc; 0xad080; 0xad08c; 0xad090; 0xad094; 0xad098; 0xad09c; 0xad0a0; 0xad0a4; 0xad13c; 0xad140; 0xad168; 0xad188; 0xad18c; 0xad190; 0xad194; 0xad198; 0xad1bc; 0xad1c8; 0xad1cc; 0xad2a8; 0xad2ac; 0xad2b4; 0xad2b8; 0xad2c0; 0xad2c4; 0xad2cc; 0xad2d0; 0xad2d4; 0xad310; 0xad354]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.
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
  Local Notation nvAr := (nvAr R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP END BUF CUR lo slo bs).
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
    lazymatch goal with |- ?g => lazymatch g with context [A_x509_get_name_C.nvA] => idtac | context [A_x509_get_name_C.nvAr] => idtac end end;
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
                        RSL : rw_cells _ mx ?sp1 (CB 16 ?j0 :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: CB 16 ?j96 :: _),
                        HKc : HK _ _ _ hc mocx, MFc : mo_frame mo0 mocx |- _ =>
      assert (Dn : nvA FB sp1 w0 w1 w2 ga gb b4 j0 j96 Lh nodes cur PHIx FFRx mx mocx hc);
      [ nvA_fin HKc MFc (mo_frame_refl mocx) |]
    end end.
  Ltac nvAr_norm :=
    match goal with RSL : rw_cells _ _ _ (CB 16 _ :: _ :: _ :: _ :: _ :: _ :: _ :: C8 (Z_to_bv 64 ?r) :: _ :: _ :: _ :: CB 16 _ :: _) |- _ =>
      is_Zlit r;
      let r' := eval vm_compute in (if Z.ltb r (2 ^ 63) then r else r - 2 ^ 64) in
      replace (Z_to_bv 64 r) with (Z_to_bv 64 r') in RSL by (apply bv_eq; vm_compute; reflexivity)
    end.
  Ltac nvAr_rebuild Dn :=
    try nvAr_norm;
    lazymatch goal with |- aevtA _ (KF _ _ _ ?hc ?mocx) _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with HHc : HM _ _ _ hc ?Lh ((?FB, 128) :: LF) mx, HCF : curFA ?nodes ?cur, HVc : havol _ _ _ hc <= _ + ?PHIx, HFRc : hfr _ _ _ hc <= _ + ?FFRx,
                        FHD : rw_cells _ mx ?FB [C8 ?w0; C8 ?w1; C8 ?w2], GA : rw_cells _ mx (?FB + 32) [C8 ?ga], GB : rw_cells _ mx (?FB + 64) [C8 ?gb],
                        FSH : rw_cells _ mx (Z.shiftr ?FB 3 + _) [_; _; _; _; C1 ?b4; _; _; _; _; _; _; _; _; _; _; _],
                        RSL : rw_cells _ mx ?sp1 (CB 16 ?j0 :: _ :: _ :: _ :: _ :: _ :: _ :: C8 (Z_to_bv 64 ?r) :: _ :: _ :: _ :: CB 16 ?j96 :: _),
                        HKc : HK _ _ _ hc mocx, MFc : mo_frame mo0 mocx |- _ =>
      assert (Dn : nvAr r FB sp1 w0 w1 w2 ga gb b4 j0 j96 Lh nodes cur PHIx FFRx mx mocx hc);
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
    mk_blob W0 W1 W2 W3 W4 HCB; nvAr_rebuild D3;
    intros moq [HKq MFq];
    eapply err_exit';
      first [ eapply nvAr_mo; [exact D3| exact HKq| exact MFq] | exact HCB | eassumption
            | lazymatch goal with
              | |- P <= _ <= END => keep; lia
              | |- _ + _ * AVOL_CALL <= _ => unfold A_x509_get_name_A.PHIn; unfold AVOL_CALL in *; keep; nia
              | |- _ + _ * fr_charge 0 <= _ => unfold A_x509_get_name_A.FFRn; keep; pose proof (Z.le_max_r 0 (fr_charge (d + 1))); pose proof (Z.le_max_l 0 (fr_charge (d + 1))); unfold fr_charge in *; nia
              | |- - 12288 < _ < 0 => first [clear; lia | keep; lia]
              end
            | match goal with |- ?g => idtac "GOERR-LEFT:" g end ].
  Ltac blo sp1 SP1x :=
    lazymatch goal with WLx : wlow _ _ _ |- _ =>
    assert (BLO : BUF + n <= sp1)
      by (pose proof (proj1 WLx BUF n (in_or_app _ _ _ (or_introl BIN))) as BL; pose proof (art_lo asegs R HIA) as ALOr;
          clear - BL ALOr SLOS SLOL SP1x SLO LOS; lia) end.

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0=60@C40858145355.279C7804676499.278 D10636937134.279D12781061969.256D16071854214.279D16901939902.279D28498761192.244D28498761192.252D35656734845.279D3953997537.256 D3953997537.258 D3953997537.262 D3953997537.263 D3953997537.292 D41869862308.243D43427672.279   D4451634193.244 D4451634193.252 D46794843979.279D60109196847.243D60109196847.244D60109196847.252D60109196847.256D60109446735.279D60189065437.256D60189065437.258D60189065437.262D60189065437.263D60189065437.292D62376725824.243D62376725824.256K12226132804.243K12226132804.256K15835051771.243K15835051771.256K15958421307.244K15958421307.252K1932217360.278 K20337545906.277K20981739667.277K21870859916.243K21870859916.256K22945712379.243K22945712379.256K23672143632.279K2431698795.244 K2431698795.252 K28077304394.279K30993319891.279K3337916572.244 K3337916572.252 K34516387472.277K40598034112.277K41252654395.244K41252654395.252K44164039966.243K44164039966.244K44164039966.252K44164039966.256K4549514449.277 K48008378065.277K48539967931.244K48539967931.252K52094252219.244K52094252219.252K59810587792.278K64038415723.244K64038415723.252K65858155712.277K67298046963.277K9840090748.244 K9840090748.252 L11152665735.148L11431517604.16 L11949961375.1  L12126572370.2  L12219316802.2  L12757185696.4  L13199423329.8  L14447267832.2  L14813823902.240L15487692983.236L15825090557.2  L15934535645.1  L15969431101.2  L16641873078.1  L16772002776.285L1685717371.0   L17523603370.285L179075641.248  L179075641.254  L1848725797.248 L1848725797.250 L1848725797.254 L1848725797.255 L1848725797.284 L18989856702.181L19072738292.245L19078215335.1  L1942461814.2   L19626383008.155L20246203949.1  L20348306388.2  L20923585658.2  L20977711877.2  L21055533038.245L21228353079.148L21654730866.2  L21868238730.2  L22353701966.7  L22938896893.2  L2310442798.148 L23182876091.2  L23292825792.2  L23657246326.2  L24023900370.0  L2419170461.2   L24587122887.181L2485050449.2   L2487147605.2   L25693330238.8  L26087448801.150L2621559066.1   L26386499879.1  L26443884051.249L26443884051.251L26443884051.255L26443884051.256L26443884051.285L27111942217.1  L27286562470.8  L27289215682.181L2784014976.3   L27897054220.3  L27940405558.8  L28074933036.3  L28632618922.2  L29010574176.233L29311754221.267L29313646868.265L29943930407.1  L30507144274.2  L3055355236.3   L30601243456.2  L30997223346.3  L31145622673.2  L31393302313.250L31393302313.252L31393302313.256L31393302313.257L31393302313.286L31789301242.2  L31936509856.236L31938607076.242L31939521696.238L33200185116.0  L3323761050.2   L33594514891.2  L34141894720.2  L34478438048.232L34522961910.2  L35139482716.0  L35497690860.3  L35497693828.3  L35499788008.3  L35627047303.1  L35662219547.1  L35666023782.10 L364199888.181  L37156630869.0  L3755151578.2   L38235734261.1  L38236685598.4  L38259954321.2  L38383890888.1  L38695569825.10 L39236637173.0  L3930512633.232 L39332637397.0  L39852159317.148L40038518010.28 L40228640085.0  L40585223510.2  L40870879649.0  L41202929119.232L41202929119.233L41202929119.241L41241644093.2  L42411609006.0  L42961455610.14 L43090580551.2  L44166661144.3  L44166924249.3  L44168742175.3  L45567083625.231L4559259063.2   L46439757434.245L47870616696.2  L47899738467.2  L48006522807.2  L48117785831.9  L48550977725.2  L49478371288.2  L49869479980.2  L50678314462.3  L50925318027.2  L51400207292.155L52108408253.2  L52516244784.241L52777546114.181L52779643270.147L52827750573.1  L52836338583.23 L5290740061.7   L52991222996.1  L53271535775.233L53271535775.241L53518955664.232L53524248224.232L53526316944.148L53526398753.150L5401337660.3   L54261998223.2  L54935543197.24 L56464645271.1  L56465858132.28 L56473405084.246L56475621844.243L56694929206.251L56694929206.253L56694929206.257L56694929206.258L56694929206.287L57128110738.147L57698627611.2  L57894927187.2  L58039649675.2  L58451383419.10 L58972524609.3  L59139600103.233L59308579414.10 L59442115284.232L59795174902.2  L60098763854.6  L60690557759.147L60812373952.10 L61672228356.279L62508983033.233L62525477031.1  L62831190464.6  L63693465645.1  L64009471222.1  L64025917085.2  L64148832490.251L64148832490.257L64148832490.258L64179129035.1  L64370849402.2  L64517051825.240L65055730314.1  L65313839333.23 L65320797075.1  L65862516566.2  L66033885980.147L66151426447.10 L66151427842.16 L66298372189.2  L66723443392.2  L66812728480.3  L67070089790.2  L67304579733.2  L68226020255.232L68519772063.1  L7735485449.2   L8171953640.251 L8171953640.257 L8171953640.258 L8175984452.232 L8176057100.237 L8176057100.243 L8178003572.148 L8178151109.234 L881835912.0    L9080220944.4   L9356559676.15  L9446628710.147 L9748633241.2   L9835808138.2   N13467909276.278N7984367253.278 N9227617910.278 N9984517160.278 O10644243082.277O10871149737.276O12822076515.277O14075571866.278O14632083704.277O14912726833.277O16962713170.279O17217116232.277O18988691132.277O21298244344.278O22525005962.277O24222861850.278O3068598504.277 O32831042147.277O32835402212.277O33449646875.277O33496826488.279O3493317847.277 O37559489567.279O3821773283.279 O39497886222.276O44938202843.277O4776649498.279 O50011839873.277O54119978487.277O55188689906.277O55209884805.277O56134767679.277O58364443802.277O64474006218.277O65961212488.277P12115299733.256P12115299733.258P12115299733.262P12115299733.263P12115299733.292P14461423358.243P14461423358.256P20934313244.277P23170010975.244P23170010975.252P23298593222.256P23298593222.258P23298593222.262P23298593222.263P23298593222.292P2770101222.276 P28627113325.256P28627113325.258P28627113325.262P28627113325.263P28627113325.292P30511339222.277P30586038854.256P30586038854.258P30586038854.262P30586038854.263P30586038854.292P3069564867.276 P31146933846.256P31146933846.258P31146933846.262P31146933846.263P31146933846.292P31778598044.279P33597136077.256P33597136077.258P33597136077.262P33597136077.263P33597136077.292P34157099334.256P34157099334.258P34157099334.262P34157099334.263P34157099334.292P38261788758.256P38261788758.258P38261788758.262P38261788758.263P38261788758.292P38605639612.257P38605639612.263P38605639612.264P38605639612.291P44164039966.256P44164039966.258P44164039966.262P44164039966.263P44164039966.292P47876372191.277P49872318794.277P50671478649.277P50927926572.277P51370907562.257P51370907562.263P51370907562.264P51370907562.291P53346601986.257P53346601986.263P53346601986.264P53346601986.291P5387390554.277 P54268551240.244P54268551240.252P57713046236.256P57713046236.258P57713046236.262P57713046236.263P57713046236.292P57883666997.277P58041177900.277P64359622428.278P66292560634.277P66738648006.256P66738648006.258P66738648006.262P66738648006.263P66738648006.292P66818508295.279P66903681610.257P66903681610.263P66903681610.264P66903681610.291P67064334489.277P7740881908.257 P7740881908.263 P7740881908.264 P7740881908.291 P7750690063.243 P7750690063.256 P9764112383.277 Q10636937134.279Q10646134994.279Q10649498890.240Q10649498890.241Q10649498890.249Q10649537205.239Q10649547784.240Q10651698952.248Q10821824020.257Q10821824020.263Q10821824020.264Q10821824020.291Q12462889934.248Q12462889935.247Q12464982158.241Q12464986477.241Q12465444467.275Q12658605510.257Q12658605510.259Q12658605510.263Q12658605510.264Q12658605510.265Q12658605510.266Q12658605510.291Q12658605510.293Q12781061969.256Q12783013201.255Q13396404662.248Q13733092405.248Q13734859144.239Q13734866741.240Q13846928860.279Q13851160440.240Q13851160440.241Q13851160440.249Q14360074768.255Q14360074768.257Q14360074768.261Q14360074768.262Q14360074768.291Q15930096381.245Q15930096381.251Q16429527224.279Q16795010073.245Q16795010073.251Q16795010073.252Q16796962909.247Q16807452132.280Q17027695041.279Q17681074618.279Q17701933584.240Q17701933584.241Q17701933584.249Q17841111261.254Q17841111261.260Q17841111261.261Q17841111261.288Q19791518367.251Q20612776491.248Q21203241386.245Q21203241386.251Q21203241386.253Q21204913491.247Q21269723930.245Q21269723930.251Q21269723930.253Q21271461859.247Q21767670690.279Q21913097236.241Q24054947262.240Q2613652986.245 Q2613652986.251 Q2613652986.253 Q2616174851.247 Q26295627581.254Q27573751300.279Q27940799286.247Q27940799287.248Q27942454161.279Q2803826605.279 Q2819779634.248 Q2819927268.242 Q28465177121.253Q28465177121.255Q28465177121.259Q28465177121.260Q28465177121.289Q28494695274.252Q28494695274.254Q28494695274.258Q28494695274.259Q28494695274.288Q28496781288.243Q28496781288.251Q28498761192.244Q28498761192.252Q29471257687.239Q29775981542.279Q30263103398.240Q3054610265.247 Q3056825117.245 Q3056825117.251 Q3056825117.252 Q3067389030.239 Q3067468761.240 Q3069291232.280 Q31524949867.252Q31526414380.257Q31526414380.263Q31526414380.264Q31526414380.291Q3215835802.252 Q3215835802.258 Q3215835802.259 Q3215835802.286 Q32681607669.279Q32681824661.256Q32681824661.258Q32681824661.262Q32681824661.263Q32681824661.292Q33137450695.279Q33283861378.257Q33283861378.263Q33283861378.264Q33283861378.291Q33342515655.253Q34357517856.251Q34357517856.257Q34357517856.258Q34357517856.285Q34390149656.240Q34390149656.241Q34390149656.249Q34669208222.252Q34669208222.258Q34669208222.259Q34669208222.286Q34964695579.250Q34964695579.256Q34964695579.257Q34964695579.284Q35294478506.248Q35294478507.247Q35656455769.247Q35656455769.253Q35656455769.254Q35656734845.279Q35658433053.279Q35662748640.246Q36719006557.240Q36915773936.245Q36915773936.251Q36915773936.253Q36918035721.247Q36986196939.245Q36986196939.251Q37149073081.256Q37149073081.258Q37149073081.262Q37149073081.263Q37149073081.292Q37216054521.241Q37216054521.249Q38053871235.239Q38372880008.249Q38372880008.255Q38372880008.256Q38372880008.283Q39180574961.256Q39180574961.258Q39180574961.262Q39180574961.263Q39180574961.292Q39600066516.240Q39600066516.241Q39600066516.249Q39721805318.245Q39721805318.251Q39721805318.253Q39723886648.242Q39723999999.247Q39724034286.248Q40354196046.257Q40354196046.263Q40354196046.264Q40354196046.291Q40360481330.242Q40360481330.248Q40360481330.249Q40360481330.276Q41675861917.245Q41677880281.281Q41688364640.246Q41688364640.252Q41688364640.253Q41867653028.242Q41869862308.243Q42222684417.254Q4230766280.255 Q4230766280.257 Q4230766280.261 Q4230766280.262 Q4230766280.291 Q42377995046.241Q42389460319.279Q42439168719.279Q42439443119.243Q42439443119.244Q42439443119.252Q42439443119.256Q42439443119.258Q42439443119.262Q42439443119.263Q42439443119.292Q42441548847.257Q42441548847.263Q42441548847.264Q42441548847.291Q42887926878.248Q42887926878.254Q42887926878.255Q42887926878.282Q42892372189.241Q43138029699.257Q43138029699.263Q43138029699.264Q43138029699.291Q43322640365.256Q43322640365.258Q43322640365.262Q43322640365.263Q43322640365.292Q43427672.279   Q43479930840.279Q43610413609.242Q43610594047.248Q44298944140.242Q44298944140.248Q44298944140.249Q44298944140.276Q44301027056.257Q44301027056.263Q44301027056.264Q44301027056.291Q4451634193.244 Q4451634193.252 Q4453582353.243 Q4453582353.251 Q45257319447.256Q45257319447.258Q45257319447.262Q45257319447.263Q45257319447.292Q45482765142.259Q45482765142.265Q45482765142.266Q45482765142.293Q45883722421.254Q46794843979.279Q47799518061.241Q47799521934.241Q47799716979.275Q47801614798.248Q47801614799.247Q48119910507.257Q48119910507.263Q48119910507.264Q48119910507.291Q49698585326.241Q49698585326.254Q50458135125.254Q5265442331.254 Q5265442331.256 Q5265442331.260 Q5265442331.261 Q5265442331.290 Q52817561962.240Q53369276613.247Q53370948668.245Q53370948668.251Q53370948668.253Q54481541668.251Q54481541668.257Q54481541668.258Q54481541668.285Q55415036769.256Q55415036769.258Q55415036769.262Q55415036769.263Q55415036769.292Q5596578838.257 Q5596578838.263 Q5596578838.264 Q5596578838.291 Q56204695986.279Q56854244147.256Q56854244147.258Q56854244147.262Q56854244147.263Q56854244147.292Q59099635219.252Q59099635219.254Q59099635219.258Q59099635219.259Q59099635219.288Q59144964087.256Q59144964087.258Q59144964087.262Q59144964087.263Q59144964087.292Q59865321072.243Q59865321072.244Q59865321072.252Q59865321072.256Q59865321072.258Q59865321072.262Q59865321072.263Q59865321072.292Q59865603600.279Q59867425008.257Q59867425008.263Q59867425008.264Q59867425008.291Q61556549392.242Q61556549392.250Q61847600945.240Q61847600945.241Q61847600945.249Q61908763639.244Q61908763639.252Q62374774592.242Q62374774592.255Q62376725824.243Q62376725824.256Q63720980196.246Q63720980196.252Q63720980196.253Q63733638937.245Q63735657309.281Q64228675114.256Q64228675114.262Q64228675114.263Q64228675114.290Q64650680438.249Q64650680438.255Q64650680438.256Q64650680438.283Q64681563910.257Q64681563910.263Q64681563910.264Q64681563910.291Q64683667846.243Q64683667846.244Q64683667846.252Q64683667846.256Q64683667846.258Q64683667846.262Q64683667846.263Q64683667846.292Q64683942374.279Q65150825229.256Q65150825229.258Q65150825229.262Q65150825229.263Q65150825229.292Q65752674778.248Q65752674778.254Q65752674778.255Q65752674778.282Q65765526873.241Q65765575771.240Q6585298697.245 Q6585298697.251 Q6585298697.253 Q6587493360.247 Q68058681330.247Q68060678923.253Q68519243108.246Q68531942553.279Q68533919965.247Q68533919965.253Q68533919965.254Q6863764061.250 Q6863764061.256 Q6863764061.257 Q6863764061.284 Q6912043747.254 Q6912043747.260 Q6912043747.261 Q6912043747.288 Q7526559625.241 Q801816838.240  Q8223186191.245 Q8223186191.251 Q8945570072.251 Q9077888740.254 Q9079820891.251 Q9080277594.252 Q9356757767.256 Q9485152634.257 Q9485152634.263 Q9485152634.264 Q9485152634.291 Q9487243258.243 Q9487243258.244 Q9487243258.252 Q9487243258.256 Q9487243258.258 Q9487243258.262 Q9487243258.263 Q9487243258.292 Q9516151461.245 Q9516151461.251 Q9644583048.279 00000400900g01g04>05^06c07h08V0;B0=30>b0@Q0BC0CC0D10E60F;0Fi0H00I<0JH0KO0LD0Nj0PU0R>0Sg0US0VS0WS0XP0YM0ZN0[O0\Q0]S0^h0`A0aY0bZ0c[0d\0e]0g20h30i40jM0k80l:0m<0nQ0oi10k11m12n14015216317L18e19g1:i1;k1<m1>B1?C1@D1A\1C11D21E31FW1G?1GD1GE1GF1GV1H21H31H41Ik1Il1Io1J01J51J61J71KF1L@1M:1Mh1NV1OD1P21P`1QN1QO1QT1QU1SR1SW1SX1SY1SZ1TH1TI1TJ1TK1Td1Te1VA1VB1VC1VD1VE1VF1VG1VH1VI1Vf1XB1XG1XL1Y:1Yh1ZV1[D1\21\61\R1]@1]A1]M1]b1]c1]d1]e1]f1]g1]h1]i1]j1]k1]l1]m1^[1_I1`71`e1aS1aT1c`1el1h81h91h:1h;1h<1je1jf1jg1jh1ji1jj1k11k61kL1l61l71lA1lE1lU1lV1l[1m81m91mg1mh1nZ1oR1oS1oT1oU20C21121_21`21a22I22O22P22Q22R23l23m24[24\24d24e25E25F25N25O25P25Q27527627d27e27f27k28X29329829f2:T2;B2=c2?X2AU2AV2AW2BL2BM2B]2D72EQ2F?2Fm2G[2HI2I72Ic2Id2Ie2If2J82JD2LP2Lg2NA2NB2NL2NM2Nj2Nk2OY2O^2P62P;2P<2P=2QK2RY2Sg2Sh2Si2TW2T\2Tj2Tk2Tl2UU2Ue2VI2VJ2VK2VL2VM2VN2W<2WA2WB2WC2WD2WE2Yn2\W2_@2a=2cf2cg2d62d[2eG2eH2eI2gN2h;2hh2iU2iV2iW2iX2iY2iZ2i[2i\2i]2i^2i_2i`2ia2ib2ic2id2ie2if2ig2ih2ii2ij2ik2il2im2in2io2kB2kC2kD2kE2kF2mg2oh32634D36e3933;L3=S3?]3Ac3D93ET3Fm3HF3Ib3Jl3MH3Ni3PH3Qg3SI3UP3Wf3YA3ZZ3\33]O3_^3b:3c[3e:3fY3h;3jB3lX3n33oL40e42A44W46247K48d4:@4<\4>=4?\4A;4B]4Ce4Dh4Ek4Fn4Gl4Hl4Ij4Jh4Ki4M94O@4Oo4Q?4RH4SL4TP4UT4Wl4YG4Zb4\=4\o4_A4aO4bI4cE4d?4e94f64g84iE4kL4l74nM4oh51A52Z54655V56Z57Y58X59W5;f5<j5=i5>h5?g5A;5BO5DV5E95E:5E]5F@5Fc5GF5Gi5HL5IK5JJ5KI5LH5Ln5MT5N:5N`5OF5PE5QV5RU5ST5Te5V65W55XJ5YC5Z<5[>5[a5\D5\g5\h5\i5\j5\k5]a5^Y5_O5`E5a>5aa5bD5cN5dG5e@5f95g25gk5hN5j]5k@5kc5lF5m;5n05ne5oZ60A60o61061161261361461561661763>65A65h65i65j65k65l66O66P68O6:N6<M6=46>S6@26@a6AP6B?6Bn6C]6DD6Dk6ER6F96F`6GZ6HT6IN6JH6Jo6KZ6M86N16Nj6Oc6P\6QC6Qj6Rc6SJ6SK6SL6SM6SN6TC6U86Um6Vb6Vc6Vd6Ve6Vf6Vg6Vh6WV6WW6WX6WY6WZ6XI6YA6Z96[16[i6[j6[k6[l6\a6]V6^K6_@6aY6cj6f;6hL6i:6ih6ja6kZ6lS6m:6n36nl6oS6oT6oU6oV6oW71572S75177279@7;N7=o7>Y7?C7?j7@c7A\7BU7CN7Ed7G?7HX7J17KM7KN7KO7KP7M@7O07P`7RP7T@7V07Vk7Wf7Xa7Y\7ZE7Zn7[W7\@7]97^27^k7_d7`]7aV7bO7c67cl7dd7eZ7fP7gI7hg7iN7j:7k<7l?7mB7nH7oI80H81G82I83M84Q85U86Y87R88K89D8:=8:d8:e8:f8:g8:h8:i8:j8:k8:l8:m8;T8=c8>F8>i8?R8@;8@d8AM8BH8CC8D>8E98F38Fm8Gg8Ha8K?8M@8ON8Q\8T=8UN8V_8X08YE8Z18ZT8[:8[`8\F8\l8]R8_i8aC8b]8d78dg8eW8f>8fn8g^8hN8i>8in8jU8jV8jW8jX8jY8lb8mn8o:90F91@92<93694094m94n94o95095195295395495595695795^96E96l97S98:9:P9;k9=D9>]9@99@:9@;9@<9@=9@>9@?9@@9@A9@B9@C9@D9@E9@F9A29A^9Bc9Ch9Dm9Dn9Do9Eh9Fa9GZ9HS9IL9JE9K>9L79M09OQ9QD9S79U[9VT9WM9XF9Y?9[`9^99`R9bk9e79gD9iT9l79n>:0R:2f:5=:7>:7?:7@:7A:7B:7C:8<:95:9n::g:;N:<5:<6:<7:<8:<9:=X:?7:@0:@i:Ab:B[:CT:DT:ET:FT:GT:HI:I>:J3:Jh:KV:LE:Md:OC:Of:PM:Q4:Q[:RG:SF:TE:UD:VC:W?:X@:YA:\4:^=:`S:bi:eR:f=:fh:gQS2PPS3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2tb3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS2FB3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB3KO0S1R3HIA1h2LF2sp2PP1P3END3CUR1d2bs3LFB3PP02B24CUR03TOP2FB3sp13cur2hc3HTc3SP13SPR2F04CPOS4SP1R3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13TOP2FB3sp13cur2hc4olen2p02e22es2q23HTc3SP13He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3CUR1d2bs3LFB3PP02B24CUR03TOP2FB3sp13cur2hc1r3HTc3SP13SPR2F04CPOS4SP1R3PPB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3CUR1d2bs3LFB3PP02B24CUR03TOP2FB3sp13cur2hc3HTc3SP13SPR2F04CPOS4SP1R3PPB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3CUR1d2bs3LFB3PP02B24CUR03TOP2FB3sp13cur2hc3HTc3SP13SPR2F04CPOS4SP1R3PPB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3CUR1d2bs3LFB3PP02B24CUR03TOP2FB3sp13cur2hc3HTc3SP12rv3SPR2F04CPOS4SP1R3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13cur2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13cur4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13cur4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13cur2tb3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3LOS2FB3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13cur1r3SP13SPR2F04CPOS4SP1R3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13cur3SP13SPR2F04CPOS4SP1R3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13cur3SP13SPR2F04CPOS4SP1R3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13cur3SP12rv3SPR2F04CPOS4SP1R3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2tb3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2tb3CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2q24CFBa3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2tb4CFBa3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur4olen2e22q23x143CPP3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur4olen2e22q23x144CFBa3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur4olen2e22q23x143APP3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2q24CFBa3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2tb4CFBa3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2q24CFBa3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2tb4CFBa3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur4olen2e22q23x143CPP3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB4olen2q23APP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB4olen2q23APP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3sp13cur4olen2e22q23x143CBF3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3DPB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur4olen2e22q23x143CPP3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur4olen2e22q23x143APP3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3cur2q23CBF3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3DPB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3DPB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3cur2tb3CBF3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur4olen2e22q23x144CFBa3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur4olen2e22q23x144CFBa3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4olen2q23CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur4olen2e22q23x143CPP3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB4olen2q23APP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB4olen2q23APP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur4olen2e22q23x143APP3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur4olen2e22q23x143CPP3PPB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB4olen2q23APP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB4olen2q23APP3PPB2HB5Ha_st5Hl_stS1R2sp2PP1P3END3BUF3CUR1d2bs3PP02B12B22B54CUR02FB3sp13cur4olen2p02q23HP03HK43SPR2F04CPOS4SP1R2LR3PPBS1R2sp3BUF2lo2bs3SLO3LOS3sp13SP13ALO3BCES3CURFFS3BUF2bs3cur3CBFS1P3END2p02e22es3Hp03He23HesFFS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B22B33DPB4CUR03DCB2D12FB3sp13cur4olen2e22es2q23He23Hes3SPR2F04CPOS4SP1R3PPB3KO0FS1lFS3curFSS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPB2HB5Ha_st5Hl_st5SAEst5CM8st2x22HxS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3sp13cur4olen2q23PPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3sp13cur4olen2q23PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2sp2PP1P3END3CUR1d2bs2FB3sp13cur3PPB2rv3HrvFS3curFS1R2sp2PP1P3END3BUF3CUR1d2bs3PP02B12B22B33B472B54CUR02FB3sp13cur4olen2p02e22es2q23He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB3KO0S3curFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBFFFS1P3BUF2B14olen2q23Hq12LRFS1R2sp2PP1P3END3BUF3CUR1d2bs3PP02B12B22B54CUR02FB3sp13cur2p02q23HP03HK43SPR2F04CPOS4SP1R3PPBFFFSFFSSS3END3BUF2bs2B32e22es3He23HesS1R2sp2PP1P3END3BUF3CUR1d2bs3PP02B12B22B54CUR02FB3sp13cur2p02q23HP03HK43SPR2F04CPOS4SP1R3PPBS3sp1S3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS2PPS1P4olen2e22q23Hq12LR2q33Hq3S1R2sp2PP1P3END3CUR1d2bs2FB3sp13cur3PPB2rv3HrvFS2PP3cur3CPPS1R2sp2lo3SLO3sp13SP1FFFFFFFFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBFS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13cur4olen2p02e22es2q23Hq13He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13cur4olen2p02e22es2q23Hq13He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13cur4olen2p02e22es2q23Hq13He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB3KO0SFFFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B472B53DPB4CUR05CURLO3DCB2D13SLO3SPH2FB3sp13cur4olen2p02e22es2q23Hq23HOL3He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPBFSSSSS5nodesS3curS1R3HIA1h2sp2lo3TOP2HTS1R2sp2PP1P3END3CUR1d2bs2FB3sp13cur3PPB2rvSS3cur4CPOSS2loS4olen2e22q23KO0FS3curS1R2sp2lo3SLO3sp13cur3SP13CLOSS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBSS1R2sp2PP1P3END3CUR1d2bs2FB3sp13cur4olen2q22LR3PPBS1P3END1d4olen2p02e22es2q23Hq13Hp03He23Hes3HP02LR2q33Hq3SFSS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBFSS1R2sp3BUF2lo2bs3SLO3LOS3sp13SP12BL4ALOrS1r2HrFFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3SPH2FB3sp13cur3SPR2F04CPOS3CLO4SP1R3PPBFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBFS2rv3HrvFS1R2sp2lo3slo4SLOS4SLOL3SLO4ALOxFS2sp3sp1FFFS1R2sp2PP1P3END3BUF3CUR1d2bs3PP02B12B22B54CUR02FB3sp13cur4olen2p02q23HP03HK43SPR2F04CPOS4SP1R2LR3PPBFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBFFS3curS1P3END1d2p02e22es2q23Hq13Hq23Hp03He23Hes3HP0S4olen2p02q23HK42LR2q34Hq3aS3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B472B53DPB4CUR05CURLO3DCB2D13SLO3SPH2FB3sp13cur2p02e22es2q23Hq13Hq23He23Hes3HP03HK43SPR2F04CPOS4SP1R3PPBS1R2sp2PP1P3END3BUF3CUR1d2bs3PP02B12B22B33B472B54CUR02FB3sp13cur2p02e22es2q23Hq23He23Hes3HP03HK43SPR2F04CPOS4SP1R3PPBS1R2sp2PP1P3END3BUF3CUR1d2bs3PP02B12B22B33B472B54CUR02FB3sp13cur4olen2p02e22es2q23He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB3KO0FFS1P3END1d4olen2p02e22es2q23Hq13HOL3Hp03He23Hes3HP02LRFS1P3END1d2rv3HrvS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3SPH2FB3sp13cur3SPR2F04CPOS3CLO4SP1R3PPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3SPH2FB3sp13cur3SPR2F04CPOS3CLO4SP1R3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2sp2PP1P3END3CUR1d2bs2FB3sp13cur1r2Hr3PPBFFFS2rv3Hrv1r3Krv1q1HS3BUF2bs3B47S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D12FB3sp13cur4olen2p02e22es2q23HOL3He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPBS1r2Hr2r02KZ1q1H2rv3HrvS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3SPH2FB3sp13cur3SPR2F04CPOS3CLO4SP1R3PPBFS1R2lo3LOSFS1R2sp2PP2lo4PPLO3SLO3sp13SP1FS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS3curS1P3END5nodes2p03CNT3KNBS3curFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPB2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPB2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPB2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS3curS1P3END1d1r2HrFFS1R2sp2PP1P3END3CUR1d2bs2FB3sp13cur1r3PPBS1r2Hr2r02Kr1q1HS3cur2r03CAL1q1r1H2H02q02H43sp14SP1MFFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS3curFFFFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B472B53DPB4CUR05CURLO3DCB2D13SLO3SPH2FB3sp13cur4olen2p02e22es2q23Hq13HOL3He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B472B53DPB4CUR05CURLO3DCB2D13SLO3SPH2FB3sp13cur4olen2p02e22es2q23Hq13He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B472B53DPB4CUR05CURLO3DCB2D13SLO3SPH2FB3sp13cur4olen2p02e22es2q23Hq13He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB3KO0S1R2sp2PP1P3END3BUF3CUR1d2bs3PP02B12B22B33B472B54CUR02FB3sp13cur4olen2p02e22es2q23HOL3He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B472B53DPB4CUR05CURLO3DCB2D13SLO3SPH2FB3sp13cur4olen2p02e22es2q23Hq13He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB3KO0SS2sp2lo3sp13SP1S1R2sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R2sp2PP1P3END3CUR1d2bs2FB3sp13cur1r2Hr3PPBFFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO03x181CS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPB3x181CS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPB3x181CS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPB3x181CFFFFFFFFFFFFFFFFFFFFFFFFFFS1R2LF2sp2PP1P3END3BUF3CUR2lo2bs3LFB3PP02B12B22B33DPB4CUR05CURLO3DCB2D13SLO3sp13SP1FFFFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B304CUR05CURLO3DCB2D13SLO3sp14olen2p02e22es2q23SP13Hq23HOL3He23Hes3HP03HK43SPR2LR3PPB3BLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO3sp12p02e22es1r3SP13Hp03He23Hes3HP03SPR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp14olen2p02e22es2q23SP12rv3He23Hes3HP03HK43ALO3SPR2LR3PPB3KO03BCE2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur2p02e22es2q23SP13Hq23He23Hes3HP03HK43SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur4olen2p02e22es2q23SP12tb3He23Hes3HP03HK43SPR3CLO2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR3CLO2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO4olen2p02e22es2q23Hq23HOL3He23Hes3HP03HK43SPR2LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO4olen2p02e22es2q23He23Hes3HP03HK43SPR2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR3CLO2LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur1r3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP12rv3SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLO3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3LOS2FB3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43ALO3SPR2F12LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp11r3SP13ALO3SPR2F13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP12rv3ALO3SPR2F13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS4olen2p02e22es2q23He23Hes3HP03HK43ALO3SPR2LR3PPB3KO03BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR3CLO2LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur1r3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP12rv3SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43ALO3SPR2LR3PPB3KO03BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3LOS2FB3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43ALO3SPR2F12LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp11r3SP13ALO3SPR2F13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP12rv3ALO3SPR2F13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR3CLO2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR3CLO2LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur1r3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP12rv3SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR3CLO2LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur1r3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP12rv3SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3LOS2FB3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43ALO3SPR2F12LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp11r3SP13ALO3SPR2F13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP12rv3ALO3SPR2F13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB1r2Hr3APB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3APB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3APB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3APB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3sp13PPB3BLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3sp11r3PPB3BLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3sp13PPB3BLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3sp13PPB3BLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3sp13PPB2rv3BLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F13PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR3CLO2LR3PPB3KO0S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB4PPLO3sp13PPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F13PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur1r2Hr4CFBa3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4CFBa3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4CFBa3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4CFBa3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB3PP02B24CUR04SLOS2FB3ALO3SPR2F13PPB2HB5Ha_st5Hl_st5SAEst3BUF2B12B33B303DPB3DCB2D14olen2p02e22es2q23He23Hes3HP03HK42LRS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB3PP02B24CUR04SLOS2FB3ALO3SPR2F13PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB3PP02B24CUR04SLOS2FB3ALO3SPR2F13PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB3PP02B24CUR04SLOS2FB3ALO3SPR2F13PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur3CLO3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO3sp14olen2p02e22es2q23SP13Hq23HOL3He23Hes3HP03HK43SPR2LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp11r3SP13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP12rv3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3cur3SPR3CLO3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS2FB3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43ALO3SPR2F12LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR3CLO2LR3PPB3KO0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP13PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR3CLO2LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur1r3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP12rv3SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B24CUR05CURLO2D13SLO3LOS3sp13SP13ALO3SPR3PPB3BCES1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB1r2Hr3APC3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APC3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APC3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APC3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43ALO3SPR2LR3PPB3KO03BCES1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB1r2Hr3APP3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APP3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APP3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APP3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3cur2q23SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3cur2tb3SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR3CLO2LR3PPB3KO0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB3BCE2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2tb3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2tb3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13SP13SPR3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp11r3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPB2rv2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLO3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43ALO3SPR2LR3PPB3KO03BCES1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP13PPBFFFFFFFFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43ALO3SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3sp14olen2p02e22es2q23SP13Hq23He23Hes3HP03HK43SPR2LR3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B22B33DPB4CUR03DCB2D14olen2e22es2q23He23Hes3SPR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B22B33DPB4CUR03DCB2D14olen2e22es2q23He23Hes3SPR3PPB3KO0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp14SP1R3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp14SP1R3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp14SP1R3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp14SP1R3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp14SP1R3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP13PPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3SPR2F03CAL4CPOS4SP1R3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stFFFFFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP13PPBFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4CPOS3PPB2HBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2FB3sp12p02e22es3SP13Hp03He23Hes3HP03SPR3PPB2HB5Ha_st5Hl_st3B304olen2q23Hq23HK42LRS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2FB3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2FB3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2FB3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP13PPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP13PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBFFFFS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B53DPB4CUR02D14olen2p02q23Hq13HP03HK43SPR2LR3PPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B53DPB4CUR02D14olen2p02q23Hq13HP03HK43SPR2LR3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B304CUR05CURLO3DCB3SLO3sp14olen2p02e22es2q23SP13Hq23HOL3He23Hes3HP03HK43SPR2LR3PPB3BLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO3sp12p02e22es1r3SP13Hp03He23Hes3HP03SPR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp14olen2p02e22es2q22rv3SP13He23Hes3HP03HK43ALO3SPR2LR3PPB3KO03BCE2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PP03PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PP03PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3LOS3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43ALO3SPR2LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS3sp11r3SP13ALO3SPR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS3sp13SP13ALO3SPR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS3sp13SP13ALO3SPR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS3sp12rv3SP13ALO3SPR3PPB2HB5Ha_st5Hl_stFFFS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D14olen2p02e22es2q23He23Hes3HP03HK43SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D14olen2p02e22es2q23He23Hes3HP03HK43SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D14olen2p02e22es2q23He23Hes3HP03HK43SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D14olen2p02e22es2q23He23Hes3HP03HK43SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D14olen2p02e22es2q23He23Hes3HP03HK43SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D14olen2p02e22es2q23He23Hes3HP03HK43SPR2LR3PPB3KO0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp11r3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPB2rv2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3SPR2F03CAL4CPOS4SP1R3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS3PPBS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS3cur2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS3sp13PPB2HB5Ha_st5Hl_st3cur2tbS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS3sp11r3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS3sp13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS3sp13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS3sp12rv3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBFFFFFFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33DPB4CUR05CURLO3SLO3LOS3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43ALO3SPR2LR3PPB3KO03BCES1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B303DPB4CUR05CURLO3SLO3sp14olen2p02e22es2q23SP13Hq23HOL3He23Hes3HP03HK43SPR2LR3PPB3BLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO3sp12p02e22es1r3SP13Hp03He23Hes3HP03SPR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO3sp14olen2p02e22es2q23SP13He23Hes3HP03HK43SPR2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33DPB4CUR05CURLO3SLO3LOS3sp14olen2p02e22es2q22rv3SP13He23Hes3HP03HK43ALO3SPR2LR3PPB3KO03BCE2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB3BCE2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4CPOS3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3ALO3SPR3PPB2HB5Ha_st5Hl_st5SAEst3BUF2B12B33B303DPB3DCB2D14olen2p02e22es2q23He23Hes3HP03HK42LRS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3ALO3SPR3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3ALO3SPR3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3ALO3SPR3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPB2HB5Ha_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPB2HB5Ha_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPB2HB5Ha_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPB2HB5Ha_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPB2HB5Ha_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPB2HB5Ha_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPB2HB5Ha_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBFFFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO2FB3SPR3PPB2HB5Ha_st5Hl_st3BUF2B12B33B303DPB3DCB2D14olen2p02e22es2q23He23Hes3HP03HK42LRS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO2FB3SPR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO2FB3SPR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO2FB3SPR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp11r3SP13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp12rv3SP13PPB2HB5Ha_st5Hl_stFFFFFFFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR3CLO2LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur1r3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur2rv3SP13SPR3CLO3PPB2HB5Ha_st5Hl_stFFFFFFFFFFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPB2HB5Ha_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPB2HB5Ha_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3ALP3PP02B22FB3sp13cur3SPR2F04SP1R3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3ALP3PP02B22FB3sp13cur3SPR2F04SP1R3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3ALP3PP02B22FB3sp13cur3SPR2F04SP1R3PPBFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2tb3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2tb3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3F643SPR2F04CPOS4SP1R3PPB2HB5Ha_st5Hl_st5SAEst2B12B33B304olen2p02e22es2q23He23Hes3HP03HK42LRS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3F643SPR2F04CPOS4SP1R3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3F643SPR2F04CPOS4SP1R3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13cur4olen2p02e22es2q23F643He23Hes3HP03HK43SPR2F04CPOS4SP1R2LR3PPB2q33Hq32HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP2FB2p02e22es3Hp03He23Hes3HP03SPR2HT3PPB2HB5Ha_st5Hl_st5SAEst3B304olen2q23Hq23HK42LRS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP2FB4olen2p02e22es2q23He23Hes3HP03HK43SPR2HT2LR3PPB3KO02HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP2FB4olen2p02e22es2q23He23Hes3HP03HK43SPR2HT2LR3PPB3KO02HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP2FB4olen2p02e22es2q23He23Hes3HP03HK43SPR2HT2LR3PPB3KO02HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP3cur2p02e22es2q23Hq23He23Hes3HP03HK43SPR2HT3PPB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP4olen2p02e22es2q23Hq23He23Hes3HP03HK43SPR2HT3PPB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP4olen2p02e22es2q23He23Hes3HP03HK43SPR2HT2LR3PPB3KO02HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13TOP3sp14olen2p02e22es2q23Hq23He23Hes3HP03HK43SPR2HT2LR3PPB2HB5Ha_st5Hl_st3cur2tb3KO0S1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP3sp12p02e22es1r3Hp03He23Hes3HP03SPR2HT3PPB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP3sp14olen2p02e22es2q23He23Hes3HP03HK43SPR2HT2LR3PPB3KO02HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP3sp14olen2p02e22es2q23He23Hes3HP03HK43SPR2HT2LR3PPB3KO02HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP3sp14olen2p02e22es2q22rv3He23Hes3HP03HK43SPR2HT2LR3PPB3KO02HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP4olen2p02e22es2q23He23Hes3HP03HK43SPR2HT2LR3PPB3KO0FFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBFFFFS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B22B33DPB4CUR03DCB2D14olen2e22es2q23He23Hes3SPR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B22B33DPB4CUR03DCB2D14olen2e22es2q23He23Hes3SPR3PPB3KO0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13SP13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13SP13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13SP13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13SP13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP13PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4CPOS3PPB2HBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B22B33DPB4CUR03DCB2D14olen2e22es2q23He23Hes3SPR3PPB3KO0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B22B33DPB4CUR03DCB2D14olen2e22es2q23He23Hes3SPR3PPB3KO0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp14SP1R3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4olen2q23PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B303DPB4CUR05CURLO3DCB2D13SLO3sp13cur4olen2p02e22es2q23SP13Hq23HOL3He23Hes3HP03HK43SPR3CLO2LR3PPB3BLO2HB5Ha_st5Hl_st2FB2tbS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO3sp13cur2p02e22es1r3SP13Hp03He23Hes3HP03SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR3CLO2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO3sp13cur4olen2p02e22es2q23SP13He23Hes3HP03HK43SPR3CLO2LR3PPB3KO02HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp13cur4olen2p02e22es2q22rv3SP13He23Hes3HP03HK43ALO3SPR3CLO2LR3PPB3KO03BCE2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4olen2q23PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2F03PPB". (* [comment removed for export] *)
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
                      (Z_to_bv 64 (Z.land cur 7)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
                      (Z_to_bv 64 (cur + 8)) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 cur) (Z_to_bv 64 es) (Z_to_bv 64 e2) t3 t4 t5 t6)
                 F (Z_to_bv 64 0xacedc) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until t6. intros D W0 W1 W2 W3 W4 PPc Hq1 Hq2 HOL Hr Hp0 He2 Hes HP0 CNT PHI FFR BUD BUDF UW KIN KOUT HK4. pose proof D as D0. nvA_open D. rt_facts. walk_prep. cur_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NRT; lia).
    assert (NN : 0 <= Z.of_nat (length nodes)) by (clear; lia).
    assert (KD : Z.of_nat (length nodes) <= NB / 6) by (assert (KNB : p0 - P <= NB) by (clear - Hp0 He2 Hes; lia); apply Z.div_le_lower_bound; [clear; lia| clear - CNT KNB; lia]).
    pose proof (bv_unsigned_in_range 64 olen) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    pose proof (rw_cells_bound _ _ _ _ PPc) as PPB. cbn [cells_size csize Nat.add length] in PPB.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    start_Wf cur FB.
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr.
    { (* [comment removed for export] *)
      zstep.
      rewrite (swrap32_land_errsum r 18446744073709542528) by (clear - Hr; lia).
      zpre.
      zstep.
      zstep. if_cases KZ; zify_cond KZ.
      - wsyncf. start_Ws cur (sp1 + 72). blo sp1 SP1. zstep. wsyncs. go_err W0 W1 W2 W3 W4 ltac:(clear - PHI FFR CNT KD Hp0 He2 Hes HP0 NN Hq1 Hq2 Hr).
      - exfalso. clear - KZ Hr. change 18446744073709551615 with (Z.ones 64) in KZ. rewrite Z.land_ones in KZ by lia. Z.div_mod_to_equations. lia. }
    assert (R0 : r = 0) by (clear - Kr Hr; change 18446744073709551615 with (Z.ones 64) in Kr; rewrite Z.land_ones in Kr by lia; Z.div_mod_to_equations; lia).
    subst r. specialize (HOL eq_refl). specialize (HK4 eq_refl). clear Kr.
    (* [comment removed for export] *)
    do 8 zstep.
    (* [comment removed for export] *)
    do 8 zstep.
    (* [comment removed for export] *)
    zstep. if_cases KO; zify_cond KO.
    { (* [comment removed for export] *)
      zstep. zstep. zstep.
      wsyncf. start_Ws cur (sp1 + 72). blo sp1 SP1. zstep. wsyncs. go_err W0 W1 W2 W3 W4 ltac:(clear - PHI FFR CNT KD Hp0 He2 Hes HP0 NN Hq1 Hq2 LR HOL). }
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_chk OBUF (q2 + bv_unsigned olen) 1.
    get_byte bs (q2 + bv_unsigned olen - BUF) tb NBt. read_at BYc NBt (q2 + bv_unsigned olen - BUF) RDt.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. if_cases KT1; zify_cond KT1.
    { (* [comment removed for export] *)
      clear RDt. zstep. zstep. zstep. zstep.
      wsyncf. start_Ws cur (sp1 + 72). blo sp1 SP1. zstep. wsyncs. go_err W0 W1 W2 W3 W4 ltac:(clear - PHI FFR CNT KD Hp0 He2 Hes HP0 NN Hq1 Hq2 LR HOL). }
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. if_cases KT2; zify_cond KT2.
    { (* [comment removed for export] *)
      clear RDt. zstep. zstep. zstep. zstep.
      wsyncf. start_Ws cur (sp1 + 72). blo sp1 SP1. zstep. wsyncs. go_err W0 W1 W2 W3 W4 ltac:(clear - PHI FFR CNT KD Hp0 He2 Hes HP0 NN Hq1 Hq2 LR HOL). }
    (* [comment removed for export] *)
    clear RDt. zstep. zstep.
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
    zstep.
    rewrite (swrap32_land_errsum rv 18446744073709542528) by (clear - Hrv; lia).
    zpre.
    zstep.
    zstep. if_cases KZ; zify_cond KZ.
    - wsyncf. start_Ws cur (sp1 + 72). blo sp1 SP1. zstep. wsyncs. go_err W0 W1 W2 W3 W4 ltac:(clear - PHI FFR CNT KD Hp0 He2 Hes HP0 NN Hq1 Hq2 LR HOL Hq3 Hrv).
    - exfalso. clear - KZ Hrv. change 18446744073709551615 with (Z.ones 64) in KZ. rewrite Z.land_ones in KZ by lia. Z.div_mod_to_equations. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
