(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_x509_get_name_A.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_len
     A_asn1_free_named_data_list_shallow A_crt_stmts A_crt_parse_stmts A_pkcs7_getcerts A_x509_get_name_stmt A_x509_get_name_stmtE A_x509_get_name_A A_x509_get_name_B A_x509_get_name_C A_x509_get_name_D A_x509_get_name_E.
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
Local Ltac zchk_new ::= constr:([0xaccb0; 0xacd44; 0xacd48; 0xacd88; 0xacd8c; 0xacd90; 0xacdc0; 0xacdc4; 0xacdc8; 0xacdcc; 0xacdd0; 0xacdd4; 0xacdd8; 0xacdf4; 0xace00; 0xace1c; 0xace20; 0xace24; 0xace28; 0xace2c; 0xace40; 0xace44; 0xace48; 0xace4c; 0xace50; 0xace54; 0xace58; 0xace5c; 0xace60; 0xace64; 0xace68; 0xace6c; 0xace70; 0xace74; 0xace78; 0xace7c; 0xace80; 0xace84; 0xace88; 0xace8c; 0xace90; 0xace94; 0xace98; 0xace9c; 0xacea0; 0xacea4; 0xacea8; 0xaceac; 0xaceb0; 0xaceb4; 0xaceb8; 0xacebc; 0xacec0; 0xacec4; 0xacec8; 0xacecc; 0xaced0; 0xacee8; 0xacf18; 0xacf20; 0xacf24; 0xacf28; 0xacf2c; 0xacf30; 0xacf34; 0xacf38; 0xacf48; 0xacf7c; 0xacf80; 0xacf84; 0xacf88; 0xacfcc; 0xacfd0; 0xacfd4; 0xacfdc; 0xacff8; 0xacffc; 0xad080; 0xad08c; 0xad090; 0xad094; 0xad098; 0xad09c; 0xad0a0; 0xad0a4; 0xad13c; 0xad140; 0xad168; 0xad180; 0xad188; 0xad18c; 0xad190; 0xad194; 0xad198; 0xad1bc; 0xad1c8; 0xad1cc; 0xad2a8; 0xad2ac; 0xad2b4; 0xad2b8; 0xad2c0; 0xad2c4; 0xad2cc; 0xad2d0; 0xad2d4; 0xad30c; 0xad310; 0xad328; 0xad350; 0xad354]).
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
                        RSL : rw_cells _ mx ?sp1 (CB 16 ?j0 :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: CB 16 ?j96 :: _),
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

  Let err_exit0' := err_exit0 R HIA IMG FREEL h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0
                     PP P END BUF CUR lo slo d bs LFB PP0 CWP PPLO BIN B1 B2 B3 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH TPV.
  Let ok_exit' := ok_exit R HIA IMG h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0
                     PP P END BUF CUR lo slo d bs LFB PP0 CWP PPLO BIN B1 B2 B3 DPB CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH.
  Let calloc_stepN' := calloc_stepN R HIA IMG h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PP END BUF CUR lo slo d bs
                         CWP PPLO BIN ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA TPV.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01R0@D11532395422.237D11532395422.250D25887797116.237D25887797116.250D60109196847.237D60109196847.250K14662993782.237K14662993782.250K44164039966.237K44164039966.250K48593550302.237K48593550302.250K52599012741.237K52599012741.250K59713869701.237K59713869701.250K64521742742.250L11949961375.1  L14373018273.5  L14647789168.2  L16641873078.1  L16855299259.1  L1685717371.0   L17995989097.225L17995989097.236L20942401132.3  L26071006300.0  L27111942217.1  L29765673068.238L33372698086.4  L35627047303.1  L35666023782.10 L37067627762.4  L37156630869.0  L38383890888.1  L39332637397.0  L40228640085.0  L4118708375.1   L44166661144.3  L47397938711.1  L48117785831.9  L48596171480.2  L52610022531.2  L57130527895.2  L57973538977.0  L59308632045.3  L59723830915.2  L60098763854.6  L62586168108.2  L64515273836.2  L7917992647.1   L9356559676.15  P57140489617.237P57140489617.250P62587740714.237P62587740714.250Q1101800120.234 Q1101800120.247 Q11530185118.236Q11530185118.249Q11532395422.237Q11532395422.250Q1343424951.234 Q1343424951.247 Q1437110698.234 Q1437110698.247 Q15249048362.234Q25024235651.233Q25024235651.246Q25887797116.237Q25887797116.250Q25890039164.236Q25890039164.249Q29624607319.233Q29624607319.246Q32352309670.234Q32352309670.247Q32681824661.237Q32681824661.250Q3848819255.234 Q3848819255.247 Q39033360938.234Q39033360938.247Q42439443119.237Q42439443119.250Q43622973458.235Q43622973458.248Q47700929126.233Q47700929126.246Q47700973017.234Q47700973017.247Q59865321072.237Q59865321072.250Q61338516829.234Q61338516829.247Q64683667846.237Q64683667846.250Q9870426295.234 00000i01d02]03X04X05Z06Q07J08A09:0:00:h0;_0<X0=O0>H0??0?D0?U0?V0?[0?`0?a0A70BR0B]0B^0Bb0D50DB0DI0D_0Dn0Do0E40E50E60E90E:0E=0E]0E^0E_0E`0Ea0Ej0Ek0F50F60F70F:0F_0Ge0Hm0J]0LO0M70M_0NN0O?0On0P_0QV0RM0S40S[0TB0Tb0UB0V10Vb0WQ0XB0Xb0YB0Z\0\;0\m0]a0^X0_O0`60`]0aU0bO0c80ca0dA0da0eA0ea0eb0ec0fC0fc0hQ0jA0kZS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur1N2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur1N2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13cur1N2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR1d2bs3LFB2FB3cur4CFBa2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR1d2bs3LFB2FB3cur1N4CFBa2HB5Ha_st5Hl_stS1R2LF2sp1P3END3BUF3CUR1d2bs3LFB3cur3CBF2HB5Ha_st5Hl_stS1R2LF2sp1P3END3BUF3CUR1d2bs3LFB3cur1N3CBF2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3CPP2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur1N3CPP2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR1d2bs3LFB2FB3cur4CFBa2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR1d2bs3LFB2FB3cur1N4CFBa2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR1d2bs3LFB2FB3cur4CFBa2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR1d2bs3LFB2FB3cur1N4CFBa2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR1d2bs3LFB3cur1N5APcur2HB5Ha_st5Hl_stS3CURS1P3END1p3Hp13Hp2FS3curS3curSS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3SPH2FB3sp13cur3SPR4SP1R2F04CPOS3CLOS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3SPH2FB3sp13cur3SPR4SP1R1N2F04CPOS3CLO2N0S3END1p3Hp2SS2PPS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PP02B24CUR02FB3sp13cur3ACV3SPR4SP1R1N2F04CPOS2N02NCS1P3END1p3Hp2S5nodesS1R3HIA1h2sp2lo3TOP2HTS1P5nodes1p3CNTSS3curSSS1NFS1NS1R2sp2lo3slo4SLOS4SLOL3SLO4ALOxFFFSS1N2N02KNFS1R2lo3LOSFFS1NS1R2sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R2LF2sp1P3END3CUR2lo1d2bs3LFB2B24CUR03SLO3cur3SPR3CLO2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR2lo1d2bs3LFB2B24CUR03SLO3cur3SPR1N3CLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB2B12B22B33DPB4CUR03DCB2D13SLO3sp13cur1p3Hp13Hp23SPR3SP13CLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB2B12B22B33DPB4CUR03DCB2D13SLO3sp13cur1p3Hp13Hp23SPR1N3SP13CLO2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR1d2bs3LFB3cur4CPOS2HBS1R2LF2sp1P3END3CUR1d2bs3LFB3cur4CPOS2HBS1R2LF2sp1P3END3CUR1d2bs3LFB3cur2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR1d2bs3LFB3cur1N2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR1d2bs3LFB3cur2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR1d2bs3LFB3cur1N2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR2lo1d2bs3LFB2B24CUR03SLO3sp13SPR3SP1S1R2LF2sp1P3END3CUR2lo1d2bs3LFB2B24CUR03SLO3sp13SPR3SP1S1R2LF2sp1P3END3CUR2lo1d2bs3LFB3sp13SP1S1R2LF2sp1P3END3CUR2lo1d2bs3LFB3sp13SP1S1R2LF2sp1P3END3CUR2lo1d2bs3LFB3sp13SP1S1R2LF2sp1P3END3CUR1d2bs3LFB3curS1R2LF2sp1P3END3CUR1d2bs3LFB3curS1R2LF2sp1P3END3CUR1d2bs3LFB3cur2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR1d2bs3LFB3cur1N2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR1d2bs3LFB3cur2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR1d2bs3LFB3cur1N2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR1d2bs3LFB3curS1R2LF2sp1P3END3CUR1d2bs3LFB3curS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3SPR4SP1R2F03CAL4CPOSS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3SPR4SP1R1N2F03CAL4CPOS2N0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur1N2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR2lo1d2bs3LFB2B24CUR03SLO3sp13SPR3SP1S1R2LF2sp1P3END3CUR2lo1d2bs3LFB2B24CUR03SLO3sp13SPR3SP1S1R2LF2sp1P3END3CUR2lo1d2bs3LFB3sp13SP1S1R2LF2sp1P3END3CUR2lo1d2bs3LFB3sp13SP1S1R2LF2sp1P3END3CUR3slo1d2bs3LFB4SLOS3cur2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR3slo1d2bs3LFB4SLOS3cur1N2HB5Ha_st5Hl_stS1R2LF2sp1P3END3CUR1d2bs3LFB3cur2HB5Ha_stS1R2LF2sp1P3END3CUR1d2bs3LFB3cur2HB5Ha_stS1R2LF2sp1P3END3CUR1d2bs3LFB3curS1R2LF2sp1P3END3CUR1d2bs3LFB3curS1R2LF2sp1P3END3CUR1d2bs3LFB3curS1R2LF2sp1P3END3CUR1d2bs3LFB3curFFS1R2LF2sp1P3END3CUR1d2bs3LFB3curS1R2LF2sp1P3END3CUR1d2bs3LFB3curS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB2B12B22B33DPB4CUR03DCB2D13TOP3cur1p3Hp13Hp23SPR2HT2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB2B12B22B33DPB4CUR03DCB2D13TOP3cur1p3Hp13Hp23SPR1N2HT2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB2B12B22B33DPB4CUR03DCB2D13SLO3sp11p3Hp13Hp23SPR3SP1". (* [comment removed for export] *)
  #[using="IMG CALLOC FREEL LFB PP0 CWP PPLO BIN B1 B2 B3 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS err_exit0' calloc_stepN'"] Lemma alloc_outer : forall FB sp1 w0 w1 w2 ga gb b4 j0 j96 nodes cur PHIx FFRx mc moc hc (J : list byte) (MG : byte) (P7 : list byte) (p : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6v s10v : word),
    nvA FB sp1 w0 w1 w2 ga gb b4 j0 j96 (nLB nodes) nodes cur PHIx FFRx mc moc hc ->
    rw_cells asegs mc cur (name_blob J 0 MG P7) ->
    rw_cells asegs mc PP [C8 (Z_to_bv 64 p)] -> P <= p -> p < END ->
    6 * (Z.of_nat (length nodes) + 1) <= p - P ->
    PHIx <= Z.of_nat (length nodes) * (2 * 64 + AVOL_CALL) -> FFRx <= Z.of_nat (length nodes) * Z.max 0 (fr_charge (d + 1)) ->
    havol asegs R HIA h + PHIn NB <= AVOL_MAX -> hfr asegs R HIA h + FFRn NB d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    OuterOb p ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (Z.land cur 7)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
                      s6v (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 cur) s10v (Z_to_bv 64 (-8)) t3 t4 t5 t6)
                 F (Z_to_bv 64 0xad130) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s10v. intros D HCB PPc Hp1 Hp2 CNT PHI FFR BUD BUDF UW KOUT. pose proof D as D0. nvA_open D. rt_facts. walk_prep. cur_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NRT; lia).
    assert (NB1 : Z.of_nat (length nodes) + 1 <= NB / 6) by (apply Z.div_le_lower_bound; [lia| clear - CNT Hp2; lia]).
    assert (NN : 0 <= Z.of_nat (length nodes)) by (clear; lia).
    unfold name_blob in HCB.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof D0 as D1'. pose proof HCB as HCB1. pose proof PPc as PPc1. rename mc into m1.
    replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R) : word) by (rewrite CALLOC; reflexivity).
    (* [comment removed for export] *)
    clear HHc HKc MFc HTc HSc HFc HCSc HVc HFRc PRES FHD GA GB FSH SAVE RSL STb STlo BYc OPP OCUR OBUF MIc SSc OCc HHD HLS HCB PPc
          CSOKc HT CFBc SCS03c SCS SCSc CRP CRC CWCc CWPc CRcur CWcur.
    eapply calloc_stepN';
      first [ exact D1' | sec_hyps | exact UW
            | lazymatch goal with
              | |- havol _ _ _ _ + _ + _ <= AVOL_MAX => clear - BUD PHI NB1 NN; unfold A_x509_get_name_A.PHIn in BUD; unfold AVOL_CALL in *; nia
              | |- hfr _ _ _ _ + _ + _ <= FR_MAX => clear - BUDF FFR NB1 NN; unfold A_x509_get_name_A.FFRn in BUDF; pose proof (Z.le_max_r 0 (fr_charge (d + 1))); pose proof (Z.le_max_l 0 (fr_charge (d + 1))); unfold fr_charge in *; nia
              | |- 0 <= _ < 2 ^ 64 => clear; lia
              | |- _ mod 2 = 0 => reflexivity
              end
            | idtac ].
    - (* [comment removed for export] *)
      intros m2 mo2 h2 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 D2 HP2.
      assert (HCB2 : rw_cells asegs m2 cur [CB 48 J; C8 (Z_to_bv 64 0); C1 MG; CB 7 P7]).
      { eapply (presA_rw_cells asegs R); [exact HP2| exact HCB1| | exact I]. cbn [cells_size csize Nat.add length].
        destruct CCASE as [->|(HIN & _)].
        - eapply (client_range_lower L _ lo); [| exact CURLO]. eapply client_range_incl; [exact (client_range_of_w L _ _ _ _ _ CWC)|].
          intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUBL; exact Hb| right; apply (fdata_cons_sub b [] FB 128 LF); exact Hb].
        - eapply client_range_block; [apply in_or_app; left; exact (SUBN _ HIN)| clear; lia| clear; lia]. }
      assert (PPc2 : rw_cells asegs m2 PP [C8 (Z_to_bv 64 p)]).
      { eapply (presA_rw_cells asegs R); [exact HP2| exact PPc1| | exact I]. cbn [cells_size csize Nat.add length].
        eapply (client_range_lower L _ lo); [| exact PPLO]. eapply client_range_incl; [exact (client_range_of_w L _ _ _ _ _ CWP)|].
        intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUBL; exact Hb| right; apply (fdata_cons_sub b [] FB 128 LF); exact Hb]. }
      clear D0 D1' HCB1 PPc1 HP2 SUBL SUBN HND HFR HCF SP1 SP1M F64 FRSH CFB F0 F1 F2 F3 APP APC APB STKH WL WCC WCP WCcur CAL CPOS CLO CPP CBF CFBa CCASE.
      pose proof D2 as D0. nvA_open D2. walk_prep. cur_prep.
      start_W cur.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      zstep.
      (* [comment removed for export] *)
      zstep.
      wsync. nvA_rebuild D3.
      intros moq [HKq MFq].
      lazymatch goal with H : rw_cells _ ?mx cur _ |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename H into HCB3 end.
      eapply err_exit0' with (J := J) (MG := MG) (P7 := P7);
        first [ eapply nvA_mo; [exact D3| exact HKq| exact MFq] | unfold name_blob; exact HCB3 | eassumption
              | lazymatch goal with
                | |- P <= p <= END => clear - Hp1 Hp2; lia
                | |- _ + _ * AVOL_CALL <= _ => clear - PHI NB1 NN; unfold A_x509_get_name_A.PHIn; unfold AVOL_CALL in *; nia
                | |- _ + _ * fr_charge 0 <= _ => clear - FFR NB1 NN; unfold A_x509_get_name_A.FFRn; pose proof (Z.le_max_r 0 (fr_charge (d + 1))); pose proof (Z.le_max_l 0 (fr_charge (d + 1))); unfold fr_charge in *; nia
                | |- - 12288 < - 10368 < 0 => clear; lia
                end
              | match goal with |- ?g => idtac "AO-ERR-LEFT:" g end ].
    - (* [comment removed for export] *)
      intros m2 mo2 h2 N y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 D2 NZ N16 NFR HP2.
      assert (HCB2 : rw_cells asegs m2 cur [CB 48 J; C8 (Z_to_bv 64 0); C1 MG; CB 7 P7]).
      { eapply (presA_rw_cells asegs R); [exact HP2| exact HCB1| | exact I]. cbn [cells_size csize Nat.add length].
        destruct CCASE as [->|(HIN & _)].
        - eapply (client_range_lower L _ lo); [| exact CURLO]. eapply client_range_incl; [exact (client_range_of_w L _ _ _ _ _ CWC)|].
          intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUBL; exact Hb| right; apply (fdata_cons_sub b [] FB 128 LF); exact Hb].
        - eapply client_range_block; [apply in_or_app; left; exact (SUBN _ HIN)| clear; lia| clear; lia]. }
      assert (PPc2 : rw_cells asegs m2 PP [C8 (Z_to_bv 64 p)]).
      { eapply (presA_rw_cells asegs R); [exact HP2| exact PPc1| | exact I]. cbn [cells_size csize Nat.add length].
        eapply (client_range_lower L _ lo); [| exact PPLO]. eapply client_range_incl; [exact (client_range_of_w L _ _ _ _ _ CWP)|].
        intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUBL; exact Hb| right; apply (fdata_cons_sub b [] FB 128 LF); exact Hb]. }
      clear D0 D1' HCB1 PPc1 HP2 SUBL SUBN HND HFR HCF SP1 SP1M F64 FRSH CFB F0 F1 F2 F3 APP APC APB STKH WL WCC WCP WCcur CAL CPOS CLO CPP CBF CFBa CCASE.
      pose proof D2 as D0. nvA_open D2. walk_prep. cur_prep.
      ddestruct (snoc_facts R HIA h LB LF PP CUR lo slo CWP CWC SLOS SLOL FB (nLB nodes) nodes cur N h2 m2 HHc (nLB_sub LB nodes) (nLB_in LB nodes) HND HFR HCF NFR N16) as (HND' & HFR' & HCF' & APcur & SUBN').
      dpose NFR as (N0 & NC & ND & NAP).
      start_W cur.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases KN; zify_cond KN. 2:{ exfalso. kland KN. rewrite ?Z.mod_small in KN by (clear - N0 NC ACV; lia). clear - KN N0. lia. }
      clear KN.
      wsync.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      lazymatch goal with H : rw_cells _ m3 cur _ |- _ => rename H into HCB3 end.
      change ([CB 48 J; C8 (Z_to_bv 64 N); C1 MG; CB 7 P7]) with (name_blob J N MG P7) in HCB3.
      pose proof (headrep_snoc CUR nodes cur m3 J MG P7 N HCF HHD HCB3) as HHD3.
      pose proof (close_fin R LB LF PP CUR FB ((N, 64) :: nLB nodes) nodes cur m3 J MG P7 N HFR HCF SUBN HLS HCB3) as HLS3.
      pose proof (hm_aobj_block asegs R HIA h2 ((N, 64) :: nLB nodes) ((FB, 128) :: LF) m3 N 64 HHc (or_introl eq_refl)) as OCN.
      rewrite <- nLB_snoc in HHc, HLS3, SUBN'.
      lazymatch goal with H : rw_cells _ m3 N _ |- _ => rename H into HNEW end.
      chunk_split HNEW 1%nat W0 HN1. chunk_split HN1 1%nat W1 HN2. chunk_split HN2 1%nat W2 HN3. chunk_split HN3 1%nat W3 W4.
      replace (N + 8 + 8) with (N + 16) in W2 by (clear; lia). replace (N + 8 + 8 + 16) with (N + 32) in W3 by (clear; lia).
      replace (N + 8 + 8 + 16 + 8) with (N + 40) in W4 by (clear; lia).
      intros moq [HKq MFq].
      assert (D3 : nvA FB sp1 w0 w1 w2 ga gb b4 j0 j96 (nLB (nodes ++ [N])) (nodes ++ [N]) N (PHIx + (2 * 64 + AVOL_CALL)) (FFRx + fr_charge (d + 1)) m3 moq h2).
      { split; [exact HHc|]. split; [exact HKq|]. split; [eapply mo_frame_trans; [exact MFc| exact MFq]|].
        split; [exact HTc|]. split; [exact HSc|]. split; [exact HFc|]. split; [exact HCSc|]. split; [exact HVc|]. split; [exact HFRc|].
        split; [exact PRES|].
        spine; first [ eassumption
                     | lazymatch goal with
                       | |- forall b, In b LB -> In b _ => exact (nLB_sub LB (nodes ++ [N]))
                       | |- name_lseg _ _ _ (removelast (nodes ++ [N])) (last (nodes ++ [N]) 0) => rewrite removelast_last, last_last; exact HLS3
                       end
                     | match goal with |- ?g => idtac "AO-D3-LEFT:" g end ]. }
      eapply KOUT; first [ exact D3 | eassumption
                        | lazymatch goal with
                          | |- rw_cells _ _ (N + 40) _ => exact W4
                          | |- P <= p => exact Hp1
                          | |- p <= END => clear - Hp2; lia
                          | |- 6 * Z.of_nat (length (nodes ++ [N])) <= p - P => rewrite length_app; cbn [length]; clear - CNT; lia
                          | |- _ <= Z.of_nat (length (nodes ++ [N])) * (2 * 64 + AVOL_CALL) => rewrite length_app; cbn [length]; clear - PHI NN; unfold AVOL_CALL in *; nia
                          | |- _ <= Z.of_nat (length (nodes ++ [N])) * Z.max 0 _ => rewrite length_app; cbn [length]; pose proof (Z.le_max_r 0 (fr_charge (d + 1))); pose proof (Z.le_max_l 0 (fr_charge (d + 1))); clear - FFR NN H H0; nia
                          end
                        | match goal with |- ?g => idtac "AO-KIN-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
