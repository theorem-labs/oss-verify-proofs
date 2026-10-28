(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_x509_get_name_A.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_len
     A_asn1_free_named_data_list_shallow A_crt_stmts A_crt_parse_stmts A_pkcs7_getcerts A_x509_get_name_stmt A_x509_get_name_stmtE A_x509_get_name_A A_x509_get_name_B A_x509_get_name_C A_x509_get_name_D A_x509_get_name_E A_x509_get_name_F.
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
  Ltac nvAr_rebuild Dn :=
    lazymatch goal with |- aevtA _ (KF _ _ _ ?hc ?mocx) _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with HHc : HM _ _ _ hc ?Lh ((?FB, 128) :: LF) mx, HCF : curFA ?nodes ?cur, HVc : havol _ _ _ hc <= _ + ?PHIx, HFRc : hfr _ _ _ hc <= _ + ?FFRx,
                        FHD : rw_cells _ mx ?FB [C8 ?w0; C8 ?w1; C8 ?w2], GA : rw_cells _ mx (?FB + 32) [C8 ?ga], GB : rw_cells _ mx (?FB + 64) [C8 ?gb],
                        FSH : rw_cells _ mx (Z.shiftr ?FB 3 + _) [_; _; _; _; C1 ?b4; _; _; _; _; _; _; _; _; _; _; _],
                        RSL : rw_cells _ mx ?sp1 (CB 16 ?j0 :: _ :: _ :: _ :: _ :: _ :: _ :: C8 (Z_to_bv 64 ?r) :: _ :: _ :: _ :: CB 16 ?j96 :: _),
                        HKc : HK _ _ _ hc mocx, MFc : mo_frame mo0 mocx |- _ =>
      let r' := eval vm_compute in (if Z.ltb r (2 ^ 63) then r else r - 2 ^ 64) in
      replace (Z_to_bv 64 r) with (Z_to_bv 64 r') in RSL by (apply bv_eq; vm_compute; reflexivity);
      assert (Dn : nvAr r' FB sp1 w0 w1 w2 ga gb b4 j0 j96 Lh nodes cur PHIx FFRx mx mocx hc);
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

  #[using="slo SLOS SLOL"] Lemma lseg_Wr : forall FB X Lh nodes cur (hc : HST asegs R HIA) mq LBn mm m1 fin,
    HM asegs R HIA hc Lh ((FB, 128) :: LF) mq -> (forall x, In x nodes -> In (x, 64) Lh) ->
    List.NoDup nodes -> nfreshA FB nodes -> curFA nodes cur ->
    name_lseg asegs mm LBn (removelast nodes) fin ->
    munch [(lo, X)] mm m1 -> wmono asegs mm m1 ->
    name_lseg asegs m1 LBn (removelast nodes) fin.
  Proof.
    clear - SLOS SLOL. intros FB X Lh nodes cur hc mq LBn mm m1 fin HH SUBN HND HFR HCF HL MU WM.
    pose proof (art_lo asegs R HIA) as ALO.
    eapply name_lseg_mem; [exact HL| intros y Hy; eapply name_lseg_in; [exact HL| exact Hy] |].
    intros y cs Hy HR Hsz. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. rewrite Hsz.
    ddestruct (others_apart R HIA LB LF PP CUR FB Lh nodes cur hc ((FB, 128) :: LF) mq y HH SUBN HND HFR HCF Hy) as ((_ & _ & YCE & _ & _ & YP & _ & _) & YC).
    cbn [disjoint_from]. lia.
  Qed.

  #[using="CURLO D1"] Lemma headrep_Wr : forall FB X nodes cur mm m1,
    nfreshA FB nodes -> curFA nodes cur ->
    headrep mm nodes -> munch [(lo, X)] mm m1 -> wmono asegs mm m1 -> headrep m1 nodes.
  Proof.
    clear - D1 CURLO. intros FB X nodes cur mm m1 HFR HCF [->|(j & g & p7 & HR)] MU WM; [left; reflexivity|].
    destruct HCF as [[-> _]|(Hne & ->)]; [left; reflexivity| right].
    pose proof (HFR _ (last_in nodes Hne)) as (_ & _ & _ & _ & _ & _ & NCU & _).
    dexists j, g, p7. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. cbn. lia.
  Qed.

  Ltac start_Wr X :=
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl [(lo, X)] mx) as MU; pose proof (wmono_refl asegs mx) as WM end.

  Ltac wsyncr :=
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with MU : munch [(lo, ?X)] ?mm mx, WM : wmono _ ?mm mx, HHD : headrep ?mm ?nodes, HLS : name_lseg _ ?mm ?Lh (removelast ?nodes) _,
                        HHc : HM _ _ _ ?hc ?Lh ((?FB, 128) :: LF) mx, HCF : curFA ?nodes ?cur, HFR : nfreshA ?FB ?nodes, HND : List.NoDup ?nodes,
                        SUBN : forall x, In x ?nodes -> In (x, 64) ?Lh |- _ =>
      let A := fresh "HHD" in let B := fresh "HLS" in
      pose proof (headrep_Wr FB X nodes cur mm mx HFR HCF HHD MU WM) as A;
      pose proof (lseg_Wr FB X Lh nodes cur hc mx Lh mm mx (last nodes 0) HHc SUBN HND HFR HCF HLS MU WM) as B;
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
              | |- - 12288 < _ < 0 => clear; lia
              end
            | match goal with |- ?g => idtac "GOERR-LEFT:" g end ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0430@D11581487313.244D28498761192.244D43219424804.243D4451634193.244 D60109196847.243D60109196847.244D62376725824.243D62376725824.244K12226132804.243K12226132804.244K15835051771.243K15835051771.244K15958421307.244K21870859916.243K21870859916.244K22945712379.243K22945712379.244K2431698795.244 K3337916572.244 K41252654395.244K44164039966.243K44164039966.244K48539967931.244K52094252219.244K64038415723.244K9840090748.244 L11949961375.1  L12219316802.2  L13199423329.8  L14447267832.2  L14948530470.7  L15825090557.2  L15934535645.1  L15969431101.2  L16641873078.1  L1685717371.0   L17027032431.23 L17027032431.8  L17266446169.7  L17993667668.232L1848725797.246 L18814368075.18 L20246203949.1  L21843175066.17 L21868238730.2  L22938896893.2  L23182876091.2  L23387882970.6  L24023900370.0  L2419170461.2   L26443884051.247L27111942217.1  L29503343994.233L31111919533.1  L31393302313.248L3323761050.2   L33692271779.241L34478491677.233L3522762990.233 L35627047303.1  L35666023782.10 L37156630869.0  L38383890888.1  L39332637397.0  L39438532713.231L39560728018.232L39941802233.233L40228640085.0  L4042219941.241 L4042221751.241 L4042222783.233 L41202929119.232L41202929119.233L41202929119.241L41241644093.2  L42411609006.0  L44166661144.3  L44168742175.3  L48026694311.9  L48117785831.9  L48550977725.2  L50874959004.0  L52108408253.2  L52827750573.1  L53271535775.233L54000129951.232L54261998223.2  L56694929206.249L56696976036.249L56696978358.249L60098763854.6  L61090611962.5  L64009471222.1  L64025917085.2  L64148832490.250L64148832490.251L65055730314.1  L7735485449.2   L8171953640.250 L8171953640.251 L8575978233.232 L9356559676.15  L9817103909.241 L9835808138.2   P14461423358.243P14461423358.244P23170010975.244P38605639612.256P38605639612.257P51370907562.256P51370907562.257P53346601986.256P53346601986.257P54268551240.244P66903681610.256P66903681610.257P7740881908.256 P7740881908.257 P7750690063.243 P7750690063.244 Q10637150594.250Q10649498890.240Q10649498890.251Q10649537205.239Q10821824020.256Q10821824020.257Q11581487313.244Q11583468241.243Q12464985715.241Q12465449928.240Q12658605510.256Q12658605510.257Q12658605510.258Q12658605510.259Q13730861759.250Q13734859144.239Q13851160440.240Q13851160440.251Q16796962909.246Q16796962909.247Q17701933584.240Q17701933584.251Q17841111261.253Q17841111261.254Q25026043070.240Q27948855020.240Q28496781288.243Q28498761192.244Q29626938986.240Q30051734150.240Q3054610265.246 Q3054610265.247 Q31299905702.241Q31526414380.256Q31526414380.257Q3215835802.251 Q3215835802.252 Q32352309670.241Q33105097987.239Q33283861378.256Q33283861378.257Q34357517856.250Q34357517856.251Q34390149656.240Q34390149656.251Q34669208222.251Q34669208222.252Q34964695579.249Q34964695579.250Q35660901081.241Q35660982493.240Q35662748640.245Q35662748640.246Q37216054521.241Q38372880008.248Q38372880008.249Q39600066516.240Q39600066516.251Q40354196046.256Q40354196046.257Q40360481330.241Q40360481330.242Q4058249799.241 Q41675861917.244Q41675861917.245Q41690659046.239Q41690695513.240Q42439443119.243Q42439443119.244Q42441548847.256Q42441548847.257Q42887926878.247Q42887926878.248Q43138029699.256Q43138029699.257Q43219424804.243Q43221703716.242Q44032153998.248Q44298944140.241Q44298944140.242Q44301027056.256Q44301027056.257Q44466681126.240Q4451634193.244 Q4453582353.243 Q45482765142.258Q45482765142.259Q47699131995.240Q47700973017.241Q47799520371.241Q47799726536.240Q48119910507.256Q48119910507.257Q49698585326.241Q49698585326.242Q54481541668.250Q54481541668.251Q55959440093.240Q5596578838.256 Q5596578838.257 Q59865321072.243Q59865321072.244Q59867425008.256Q59867425008.257Q61338516829.241Q61556549392.242Q61847600945.240Q61847600945.251Q61908763639.244Q62374774592.242Q62374774592.243Q62376725824.243Q62376725824.244Q63733638937.244Q63733638937.245Q64182165048.240Q64228675114.255Q64228675114.256Q64650680438.248Q64650680438.249Q64681563910.256Q64681563910.257Q64683667846.243Q64683667846.244Q65752674778.247Q65752674778.248Q68519243108.245Q68519243108.246Q68521614429.241Q6863764061.249 Q6863764061.250 Q6912043747.253 Q6912043747.254 Q9200000471.239 Q9476649719.248 Q9485152634.256 Q9485152634.257 Q9487243258.243 Q9487243258.244 00000m02203204705>06J07J08G09D0:>0;?0<=0=?0>@0?>0@?0A=0B>0C@0DB0EC0FM0GO0HQ0IR0JS0JX0JY0K50K60KI0KJ0KM0KN0KS0KT0LI0Lc0M70NQ0O?0OU0OZ0P00P10P20P30PC0PD0PE0Q30Q70Qe0Qj0RX0RY0U70W\0XJ0XQ0Xg0Xh0Xm0Xn0ZH0[b0\P0\Q0_30aN0d70de0eS0fA0fB0fC0fD0fE0fd0gD0gE0gF0gG0gL0h:0hh0hi0iW0jE0k30k=0kO0kP0kQ0l_0mm0n20n30n40n50nc0oH11_11`14216=18?19B1:E1;I1<M1=d1?;1AE1BD1CC1DB1EA1FQ1G^1HA1Hd1IG1Ij1Ji1Kh1L^1MT1N:1N`1O_1P^1Qo1S@1Sc1TF1TG1TH1UA1V:1V]1W@1X51Xj1YQ1Z81[21[l1\S1]B1^;1_41`R1`S1`T1aI1b>1dC1dj1dk1dl1ed1f\1f]1f^1gS1hH1jN1l[1mB1mi1nb1o[20E21>22722822923423o24X25A26026i27b28I2902:22;92<=2=A2>:2?32?42?52?n2@g2AN2B72B`2C[2DV2F42Fn2Gh2I92JJ2K12KX2L>2Ld2N:2OP2P@2Q02R82S@2Sg2Sh2Si2Sj2Sk2Sl2Sm2TT2U@2VE2WJ2WK2XD2Y:2Z32Zi2[b2\[2]B2_\2aO2bH2cA2eO2gd2j42lD2m=2n62no2oh30O31O32O33D34934`35G36F37E38A39BS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur4vlen2q33PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2q33PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur4vlen2q33PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13cur2q33PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13cur4vlen2q33PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2q33PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2q33CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2q34CFBa3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4CFBa3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4vlen2q33CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2q34CFBa3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4CFBa3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2q34CFBa3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4CFBa3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB4vlen2q33APP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4vlen2q33CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4vlen2q33CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3cur2q33CBF3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3DPB4vlen2q33PPB2HB5Ha_st5Hl_st3cur3CBFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4vlen2q33CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4vlen2q33CPP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB4vlen2q33APP3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB4vlen2q33APP3PPB2HB5Ha_st5Hl_stS3CURFS1P3END2p02e22es3Hp03He23HesFS4vlen2es2q33He22KSFS1lFS3curSS1P3END1d4vlen2p02e22es2q33Hq13Hq23Hp03He23Hes3HP02LRS1P3END4vlen2q33Hq13Hes2LRS3END4vlen2q33Hes2KES1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3SPH2FB3sp13cur3SPR2F04CPOS3CLO4SP1R3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS2bs4vlen2e22q33Hq22KMS3curS2bs4vlen2es2q33He22KSFFFS4vlen2p02q33Hp0SFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS2PPS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B472B53DPB4CUR05CURLO3DCB2D13SLO3SPH2FB3sp13cur4vlen2p02es2q33He23Hes3HP03HK63SPR2F04CPOS4SP1R2LR3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B472B53DPB4CUR05CURLO3DCB2D13SLO3SPH2FB3sp13cur4vlen2p02e22es2q33Hq23He23Hes3HP03HK63SPR2F04CPOS4SP1R2LR3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS5nodesS1R3HIA1h2sp2lo3TOP2HTSS3curSS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3SPH2FB3sp13cur3SPR2F04CPOS3CLO4SP1R3PPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3SPH2FB3sp13cur3SPR2F04CPOS3CLO4SP1R3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBSS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B472B53DPB4CUR05CURLO3DCB2D13SLO3SPH2FB3sp13cur4vlen2p02es2q33Hq13He23Hes3HP03HK63SPR2F04CPOS4SP1R2LR3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B472B53DPB4CUR05CURLO3DCB2D13SLO3SPH2FB3sp13cur4vlen2p02q33Hq13Hes3HP03HK63SPR2F04CPOS4SP1R2LR3PPBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B472B53DPB4CUR05CURLO3DCB2D13SLO3SPH2FB3sp13cur4vlen2p02e22es2q33Hq13Hq23He23Hes3HP03HK63SPR2F04CPOS4SP1R2LR3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBFSFFS1P5nodes4vlen2p02q33CNT3HK62LRS1R2sp2lo3slo4SLOS4SLOL3SLO4ALOxFSFS3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2lo3LOSS1P4vlen2q33Hq12LRFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPB2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPB2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS3curFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur3PPBS1R2sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B472B53DPB4CUR05CURLO3DCB2D13SLO3SPH2FB3sp13cur4vlen2p02q33Hes3HP03HK63SPR2F04CPOS4SP1R2LR3PPBFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB2B12B22B33DPB4CUR03DCB2D13SLO3sp13cur4vlen2p02e22es2q33SP13Hq23He23Hes3HP03HK63SPR3CLO2LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB2B12B22B33DPB4CUR03DCB2D13SLO3sp13cur4vlen2p02es2q33SP13He23Hes3HP03HK63SPR3CLO2LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB4PPLO2B12B22B34CUR05CURLO3SLO4vlen2p02e22es2q33Hq23He23Hes3HP03HK63SPR2LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3APB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3APB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4CFBa3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4CFBa3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB2B24CUR04SLOS2FB3ALO3SPR2F13PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB2B24CUR04SLOS2FB3ALO3SPR2F13PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB4PPLO2B12B22B34CUR05CURLO3SLO3sp14vlen2p02e22es2q33SP13Hq23He23Hes3HP03HK63SPR2LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APC3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APC3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APP3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APP3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2B24CUR03SLO3cur2q33SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2B24CUR03SLO3cur3SPR3CLO3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4vlen2q33PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4vlen2q33PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4CPOS3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3SPR2F03CAL4CPOS4SP1R3PPBFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13cur4vlen2p02es2q33He23Hes3HP03HK63SPR2F03CAL4CPOS4SP1R2LR3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB2B12B22B33DPB4CUR03DCB2D13SLO2FB3sp14vlen2p02es2q33SP13He23Hes3HP03HK63SPR2LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB2B12B22B33DPB4CUR03DCB2D13SLO2FB3sp14vlen2p02e22es2q33SP13Hq23He23Hes3HP03HK63SPR2LR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PP03PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4CPOS3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS3cur2q33PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS4vlen2q33PPB2HB5Ha_st5Hl_st3curS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2q33PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2q33PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3SPR2F03CAL4CPOS4SP1R3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4vlen2q33PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB4vlen2q33PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2B24CUR03SLO3LOS2FB3ALO3SPR3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2B24CUR03SLO3LOS2FB3ALO3SPR3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPB2HB5Ha_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPB2HB5Ha_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2B24CUR03SLO2FB3SPR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2B24CUR03SLO2FB3SPR3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBFFFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PPB2HB5Ha_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3ALP3PP02B22FB3sp13cur3SPR2F04SP1R3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3ALP3PP02B22FB3sp13cur3SPR2F04SP1R3PPBFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2q33PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2q33PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13cur4vlen2p02es2q33F643He23Hes3HP03HK63SPR2F04CPOS4SP1R2LR3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3F643SPR2F04CPOS4SP1R3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB2B12B22B33DPB4CUR03DCB2D13TOP2FB4vlen2p02es2q33He23Hes3HP03HK63SPR2HT2LR3PPB2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB2B12B22B33DPB4CUR03DCB2D13TOP2FB4vlen2p02e22es2q33Hq23He23Hes3HP03HK63SPR2HT2LR3PPB2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB2B12B22B33DPB4CUR03DCB2D13TOP3cur4vlen2p02e22es2q33Hq23He23Hes3HP03HK63SPR2HT2LR3PPB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB2B12B22B33DPB4CUR03DCB2D13TOP4vlen2p02e22es2q33Hq23He23Hes3HP03HK63SPR2HT2LR3PPB2HB5Ha_st5Hl_st3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13SP13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13SP13PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur3PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13PPBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur3PPB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2q33PPB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4vlen2q33PPB2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG CALLOC FREEL LFB ALP PP0 CWP PPLO HBY BIN B1 B2 B3 B47 B5 B30 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS err_exit' ok_exit' alloc_inner' alloc_outer'"] Lemma l3_walk : forall FB sp1 w0 w1 w2 ga gb b4 j0 j96 nodes cur PHIx FFRx mc moc hc
      (otw : word) (r0 : list byte) (olen : word) (op : Z) (vtw : word) (r1 : list byte) (vlen : word) (j2 : list byte) (mg' : byte) (p7 : list byte)
      (p0 e2 es q3 : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    nvA FB sp1 w0 w1 w2 ga gb b4 j0 j96 (nLB nodes) nodes cur PHIx FFRx mc moc hc ->
    rw_cells asegs mc cur [C4 otw; CB 4 r0] -> rw_cells asegs mc (cur + 8) [C8 olen] ->
    rw_cells asegs mc (cur + 16) [C8 (Z_to_bv 64 op); C4 vtw; CB 4 r1] ->
    rw_cells asegs mc (cur + 32) [C8 vlen] -> rw_cells asegs mc (cur + 40) [CB 8 j2; C8 (Z_to_bv 64 0); C1 mg'; CB 7 p7] ->
    rw_cells asegs mc PP [C8 (Z_to_bv 64 q3)] -> P <= q3 -> bv_unsigned vlen <= e2 - q3 -> p0 < e2 -> e2 <= es -> es <= END -> P <= p0 ->
    6 * Z.of_nat (length nodes) <= p0 - P ->
    PHIx <= Z.of_nat (length nodes) * (2 * 64 + AVOL_CALL) -> FFRx <= Z.of_nat (length nodes) * Z.max 0 (fr_charge (d + 1)) ->
    havol asegs R HIA h + PHIn NB <= AVOL_MAX -> hfr asegs R HIA h + FFRn NB d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    (forall p' es', p0 < p' -> InnerOb p' es') -> (forall p', p0 < p' -> OuterOb p') ->
    p0 + 6 <= q3 ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (Z.land cur 7)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
                      (Z_to_bv 64 (cur + 32)) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 cur) (Z_to_bv 64 es) (Z_to_bv 64 e2) t3 t4 t5 t6)
                 F (Z_to_bv 64 0xad04c) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until t6. intros D W0 W1 W2 W3 W4 PPc Hq1 Hq2 Hp0 He2 Hes HP0 CNT PHI FFR BUD BUDF UW KIN KOUT HK6. pose proof D as D0. nvA_open D. rt_facts. walk_prep. cur_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NRT; lia).
    assert (NN : 0 <= Z.of_nat (length nodes)) by (clear; lia).
    assert (KD : Z.of_nat (length nodes) <= NB / 6) by (apply Z.div_le_lower_bound; [lia| clear - CNT Hp0 He2 Hes; lia]).
    pose proof (bv_unsigned_in_range 64 vlen) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    pose proof (rw_cells_bound _ _ _ _ PPc) as PPB. cbn [cells_size csize Nat.add length] in PPB.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    start_Wf cur FB.
    (* [comment removed for export] *)
    do 9 zstep. do 7 zstep.
    (* [comment removed for export] *)
    zstep. if_cases KM; zify_cond KM.
    { (* [comment removed for export] *)
      zstep. zstep. zpre; step; zsimp.
      wsyncf. start_Wr (sp1 + 72).
      assert (BLO : BUF + n <= sp1)
        by (pose proof (proj1 WL BUF n (in_or_app _ _ _ (or_introl BIN))) as BL; pose proof (art_lo asegs R HIA) as ALOr;
            clear - BL ALOr SLOS SLOL SP1 SLO LOS; lia).
      zpre. wsyncr.
      go_err W0 W1 W2 W3 W4 ltac:(clear - PHI FFR CNT KD Hp0 He2 Hes HP0 NN Hq1 Hq2 LR). }
    try kland KM. rewrite ?Z.mod_small in KM by (clear - LR Hq1 Hq2 He2 Hes B1 B3 B47 B5; lia).
    assert (Ee2 : e2 = q3 + bv_unsigned vlen) by (clear - KM LR Hq1 Hq2 He2 Hes B1 B3 B47 B5; lia). subst e2. try clear KM.
    (* [comment removed for export] *)
    do 7 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    wsyncf.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KS; zify_cond KS.
    - (* [comment removed for export] *)
      try kland KS. rewrite ?Z.mod_small in KS by (clear - LR Hq1 Hq2 He2 Hes B1 B3 B47 B5; lia).
      assert (Ees : es = q3 + bv_unsigned vlen) by (clear - KS LR Hq1 Hq2 He2 Hes B1 B3 B47 B5; lia). subst es. try clear KS.
      zstep. zstep. if_cases KE; zify_cond KE.
      + (* [comment removed for export] *)
        try kland KE. rewrite ?Z.mod_small in KE by (clear - LR Hq1 Hq2 He2 Hes B1 B2 B3 B47 B5; lia).
        mk_blob W0 W1 W2 W3 W4 HCB. nvA_rebuild D3.
        intros moq [HKq MFq].
        eapply ok_exit';
          first [ eapply nvA_mo; [exact D3| exact HKq| exact MFq] | exact HCB | eassumption
                | lazymatch goal with
                  | |- P <= _ <= END => clear - Hq1 Hq2 LR Hes; lia
                  | |- Z.of_nat (length nodes) <= A_x509_get_name_A.CNTn NB => unfold A_x509_get_name_A.CNTn; exact KD
                  | |- _ = END => first [exact KE | clear - KE LR Hq1 Hq2 He2 Hes B1 B2 B3 B47 B5; lia]
                  | |- PHIx <= A_x509_get_name_A.PHIn NB => unfold A_x509_get_name_A.PHIn; clear - PHI KD NN; unfold AVOL_CALL in *; nia
                  | |- FFRx <= A_x509_get_name_A.FFRn NB d => unfold A_x509_get_name_A.FFRn; pose proof (Z.le_max_r 0 (fr_charge (d + 1))); pose proof (Z.le_max_l 0 (fr_charge (d + 1))); clear - FFR KD NN H H0; unfold fr_charge in *; nia
                  end
                | match goal with |- ?g => idtac "L3-OK-LEFT:" g end ].
      + (* [comment removed for export] *)
        try kland KE. rewrite ?Z.mod_small in KE by (clear - LR Hq1 Hq2 He2 Hes B1 B2 B3 B47 B5; lia).
        mk_blob W0 W1 W2 W3 W4 HCB. nvA_rebuild D3.
        intros moq [HKq MFq].
        eapply alloc_outer';
          first [ eapply nvA_mo; [exact D3| exact HKq| exact MFq] | exact HCB | exact BUD | exact BUDF | exact UW | eassumption
                | lazymatch goal with
                  | |- P <= _ => clear - Hq1 LR; lia
                  | |- _ < END => clear - KE Hes LR Hq2; lia
                  | |- 6 * (Z.of_nat (length nodes) + 1) <= _ - P => clear - CNT HK6 LR Hq2; lia
                  | |- A_x509_get_name_E.OuterOb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply KOUT; clear - Hp0 LR Hq2; lia
                  end
                | match goal with |- ?g => idtac "L3-AO-LEFT:" g end ].
    - (* [comment removed for export] *)
      try kland KS. rewrite ?Z.mod_small in KS by (clear - LR Hq1 Hq2 He2 Hes B1 B3 B47 B5; lia).
      zpre.
      mk_blob W0 W1 W2 W3 W4 HCB. nvA_rebuild D3.
      intros moq [HKq MFq].
      eapply alloc_inner';
        first [ eapply nvA_mo; [exact D3| exact HKq| exact MFq] | exact HCB | exact BUD | exact BUDF | exact UW | eassumption
              | lazymatch goal with
                | |- P <= _ => clear - Hq1 LR; lia
                | |- _ < es => clear - KS He2 LR Hq2; lia
                | |- es <= END => exact Hes
                | |- 6 * (Z.of_nat (length nodes) + 1) <= _ - P => clear - CNT HK6 LR Hq2; lia
                | |- A_x509_get_name_E.InnerOb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply KIN; clear - Hp0 LR Hq2; lia
                end
              | match goal with |- ?g => idtac "L3-AI-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
