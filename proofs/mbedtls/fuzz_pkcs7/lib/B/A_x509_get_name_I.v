(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_x509_get_name_A.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_len
     A_asn1_free_named_data_list_shallow A_crt_stmts A_crt_parse_stmts A_pkcs7_getcerts A_mpi_stmtA A_x509_get_name_stmt A_x509_get_name_stmtE A_x509_get_name_A A_x509_get_name_B A_x509_get_name_C A_x509_get_name_D A_x509_get_name_E A_x509_get_name_F A_x509_get_name_G A_x509_get_name_H.
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
Ltac post_callA_keep segs m MUk WMk :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MIc := fresh "MI" in
  destruct PO as [E [MUk [WMk PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUk with
  | munch _ m ?m' =>
      transport_after_callA segs m m' MUk;
      transport_after_call segs m m' MUk WMk;
      try match goal with H : mem_inv segs m |- _ => clear H end
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ])
  end).

Tactic Notation "acallxA_sp_keep" constr(e) ident(MUk) ident(WMk) tactic3(apptac) :=
  lazymatch goal with
  | |- aevtA ?segs (KF _ ?R ?HIA ?h ?mo0) _ (MS _ _ _ _ _ ?m _) =>
      eapply (aevtA_cut_evtA_KF segs R HIA h mo0);
      [ apptac
      | lazymatch goal with |- forall x, ?P x -> _ => let hd := head_of P in try unfold hd end;
        rewrite ?(unsigned_lit e) by qlia; post_callA_keep segs m MUk WMk ]
  end.


From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0xad2bc; 0xace60]).
Local Ltac zchk_new ::= constr:([0xaccb0; 0xacd44; 0xacd48; 0xacd88; 0xacd8c; 0xacd90; 0xacdc0; 0xacdc4; 0xacdc8; 0xacdcc; 0xacdd0; 0xacdd4; 0xacdd8; 0xacdf4; 0xace00; 0xace1c; 0xace20; 0xace24; 0xace28; 0xace2c; 0xace40; 0xace48; 0xace50; 0xace54; 0xace58; 0xace5c; 0xace60; 0xace64; 0xace68; 0xace6c; 0xace70; 0xace74; 0xace78; 0xace7c; 0xace80; 0xace84; 0xace88; 0xace8c; 0xace90; 0xace94; 0xace98; 0xace9c; 0xacea0; 0xacea8; 0xaceac; 0xaceb0; 0xaceb8; 0xacebc; 0xacec0; 0xacec4; 0xacec8; 0xacecc; 0xaced0; 0xacee8; 0xacf18; 0xacf20; 0xacf24; 0xacf28; 0xacf2c; 0xacf30; 0xacf34; 0xacf38; 0xacf48; 0xacf7c; 0xacf80; 0xacf84; 0xacf88; 0xacfcc; 0xacfd0; 0xacfd4; 0xacfdc; 0xacff8; 0xacffc; 0xad080; 0xad08c; 0xad090; 0xad094; 0xad098; 0xad09c; 0xad0a0; 0xad0a4; 0xad13c; 0xad140; 0xad168; 0xad188; 0xad18c; 0xad190; 0xad194; 0xad198; 0xad1bc; 0xad1c8; 0xad1cc; 0xad2a8; 0xad2ac; 0xad2b4; 0xad2b8; 0xad2c0; 0xad2c4; 0xad2cc; 0xad2d0; 0xad2d4; 0xad310; 0xad354]).
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

  Let l2_walk' := l2_walk R HIA IMG CALLOC FREEL h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PP P END BUF CUR lo slo d bs
                    LFB ALP PP0 CWP PPLO HBY BIN B1 B2 B3 B47 B5 B30 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV.

  (* [comment removed for export] *)
  Definition Wsf (cur sp1 FB : Z) : list ivl := [(PP, PP + 8); (cur, cur + 64); (lo, sp1); (FB, FB + 128)].

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L41307674947.3900000mS1R2PP2lo3slo4SLOS4SLOL2FB3sp13cur3ALO1y2cs3Hsz3YCE2YP3YFB2YC". (* [comment removed for export] *)
  #[using="slo SLOS SLOL"] Lemma lseg_Wsf : forall FB sp1 Lh nodes cur (hc : HST asegs R HIA) mq LBn mm m1 fin,
    HM asegs R HIA hc Lh ((FB, 128) :: LF) mq -> (forall x, In x nodes -> In (x, 64) Lh) ->
    List.NoDup nodes -> nfreshA FB nodes -> curFA nodes cur ->
    name_lseg asegs mm LBn (removelast nodes) fin ->
    munch (Wsf cur sp1 FB) mm m1 -> wmono asegs mm m1 ->
    name_lseg asegs m1 LBn (removelast nodes) fin.
  Proof.
    clear - SLOS SLOL. intros FB sp1 Lh nodes cur hc mq LBn mm m1 fin HH SUBN HND HFR HCF HL MU WM.
    pose proof (art_lo asegs R HIA) as ALO.
    eapply name_lseg_mem; [exact HL| intros y Hy; eapply name_lseg_in; [exact HL| exact Hy] |].
    intros y cs Hy HR Hsz. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. rewrite Hsz.
    ddestruct (others_apart R HIA LB LF PP CUR FB Lh nodes cur hc ((FB, 128) :: LF) mq y HH SUBN HND HFR HCF Hy) as ((_ & _ & YCE & _ & _ & YP & _ & YFB) & YC).
    cbn [disjoint_from Wsf]. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L36143451950.2300000YS2PP3CUR2lo5CURLO2D12FB3sp15nodes3APC3NCU". (* [comment removed for export] *)
  #[using="CURLO D1"] Lemma headrep_Wsf : forall FB sp1 nodes cur mm m1,
    nfreshA FB nodes -> curFA nodes cur -> (FB + 128 <= CUR \/ CUR + 64 <= FB) ->
    headrep mm nodes -> munch (Wsf cur sp1 FB) mm m1 -> wmono asegs mm m1 -> headrep m1 nodes.
  Proof.
    clear - D1 CURLO. intros FB sp1 nodes cur mm m1 HFR HCF APC [->|(j & g & p7 & HR)] MU WM; [left; reflexivity|].
    destruct HCF as [[-> _]|(Hne & ->)]; [left; reflexivity| right].
    pose proof (HFR _ (last_in nodes Hne)) as (_ & _ & _ & _ & _ & _ & NCU & _).
    dexists j, g, p7. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. cbn. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L28573892092.1000000SS2PP2lo3cur3sp12FB4LENP3Hlo2HL1x2Hx". (* [comment removed for export] *)
  #[using="Type"] Lemma subfp_gt : forall cur sp1 FB LENP,
    lo <= sp1 - 16 ->
    (cur <= LENP /\ LENP + 8 <= cur + 64) \/ (FB <= LENP /\ LENP + 8 <= FB + 128) ->
    sub_fp [(PP, PP + 8); (LENP, LENP + 8); (sp1 - 16, sp1)] (Wsf cur sp1 FB).
  Proof. clear. intros cur sp1 FB LENP Hlo HL x Hx. unfold Wsf in Hx. cbn [outside] in *. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac start_Wsf cur sp1 FB :=
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl (Wsf cur sp1 FB) mx) as MU; unfold Wsf in MU; pose proof (wmono_refl asegs mx) as WM end.

  Ltac wsyncsf :=
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with MU : munch [_; _; (lo, ?sp1); (?FB, _)] ?mm mx, WM : wmono _ ?mm mx, HHD : headrep ?mm ?nodes, HLS : name_lseg _ ?mm ?Lh (removelast ?nodes) _,
                        HHc : HM _ _ _ ?hc ?Lh _ mx, HCF : curFA ?nodes ?cur, HFR : nfreshA ?FB ?nodes, HND : List.NoDup ?nodes,
                        SUBN : forall x, In x ?nodes -> In (x, 64) ?Lh, APC : ?FB + 128 <= CUR \/ CUR + 64 <= ?FB |- _ =>
      let A := fresh "HHD" in let B := fresh "HLS" in
      pose proof (headrep_Wsf FB sp1 nodes cur mm mx HFR HCF APC HHD MU WM) as A;
      pose proof (lseg_Wsf FB sp1 Lh nodes cur hc mx Lh mm mx (last nodes 0) HHc SUBN HND HFR HCF HLS MU WM) as B;
      clear HHD HLS MU WM; rename A into HHD; rename B into HLS
    end end.

  (* [comment removed for export] *)
  Ltac gt_sync MUk WMk cur sp1 FB LENP :=
    let SF := fresh "SF" in
    assert (SF : sub_fp [(PP, PP + 8); (LENP, LENP + 8); (sp1 - 16, sp1)] (Wsf cur sp1 FB));
    [ apply subfp_gt;
      [ lazymatch goal with SP1' : bv_unsigned sp - 240 <= sp1 <= _ |- _ => clear - SLO SP1' NS1 NRT; unfold A_x509_get_name_A.STKn in SLO; lia end
      | first [ left; clear; lia | right; clear; lia ] ] |];
    pose proof (munch_weaken _ _ _ _ SF MUk) as MU; unfold Wsf in MU;
    clear SF MUk; rename WMk into WM; wsyncsf.

  (* [comment removed for export] *)
  Ltac gt_side CBOX OL ABc BCE :=
    first [ exact (proj1 CBOX) | exact (proj1 (proj2 CBOX)) | exact (proj1 (proj2 (proj2 CBOX))) | exact OL | exact ABc | exact (art_alwf asegs R HIA)
          | exact ALP | exact PP0 | exact B5 | reflexivity
          | lazymatch goal with
            | |- bytes_at _ _ BUF bs => eassumption
            | |- aobj _ _ _ _ PP 8 => eassumption
            | |- aobj _ _ _ _ BUF _ => eassumption
            | |- cs_ok _ _ => eassumption
            | |- mem_inv _ _ => eassumption
            | |- _ = 0 \/ PP + 8 <= BUF \/ _ => right; exact DPB
            | |- BUF + _ < 2 ^ 63 => clear - B47; lia
            | |- lo <= _ - 16 => lazymatch goal with SP1' : bv_unsigned sp - 240 <= _ <= _ |- _ => clear - SLO SP1' NS1 NRT; unfold A_x509_get_name_A.STKn in SLO; lia end
            | |- _ mod 16 = 0 => lazymatch goal with SP1M' : _ mod 32 = 0 |- _ => clear - SP1M'; Z.div_mod_to_equations; lia end
            | |- crange _ lo _ => lazymatch goal with SC : crange (hcs asegs R HIA _) lo (bv_unsigned sp - lo), SP1' : bv_unsigned sp - 240 <= _ <= _ |- _ => eapply crange_sub; [exact SC| clear; lia| clear - SP1'; lia] end
            | |- PP + 8 <= _ - 16 \/ _ => left; lazymatch goal with SP1' : bv_unsigned sp - 240 <= _ <= _ |- _ => clear - PPLO SLO SP1' NS1 NRT; unfold A_x509_get_name_A.STKn in SLO; lia end
            | |- _ = 0 \/ BUF + _ <= _ - 16 \/ _ => right; left; lazymatch goal with SP1' : bv_unsigned sp - 240 <= _ <= _, ALO' : alloc_ceiling <= arl_stklo R |- _ => clear - BCE ALO' LOS SLO SP1' NS1 NRT; unfold A_x509_get_name_A.STKn in SLO; lia end
            end ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "09M0@D10636937134.267D10636937134.295D10780387598.267D10916531869.278D16071854214.267D16071854214.295D16901939902.267D16901939902.295D2457516971.267 D25887797116.278D32458870384.267D3953997537.274 D3953997537.276 D46794843979.267D46794843979.295D60109196847.278D60109446735.267D60109446735.295D60189065437.274D60189065437.276D65752989693.295D8009443288.295 K11185843281.295K14662993782.278K1932217360.267 K1932217360.295 K19511088946.295K20592461617.267K20981739667.267K20981739667.295K23672143632.267K23672143632.295K29378133114.267K30993319891.267K30993319891.295K34516387472.267K35028229553.267K36444357201.295K40598034112.267K40598034112.295K44164039966.278K45872506161.267K48593550302.278K49541715106.267K52599012741.278K56730913969.267K57332385994.295K59713869701.278K59810587792.267K59810587792.295K65858155712.295K67298046963.267K67298046963.295L10660966017.8  L11179310391.2  L11301983443.2  L11431517604.16 L11447730086.317L11949961375.1  L12126572370.2  L12140462837.3  L12140532298.162L13199424673.6  L14647789168.2  L15471821837.261L15479883060.4  L15934535645.1  L16641873078.1  L16772002776.268L16772002776.269L1685717371.0   L17523603370.268L17523603370.269L17723511885.5  L1848725797.266 L1848725797.268 L18529518550.275L18549529655.5  L1942461814.2   L19497174612.2  L19914454641.3  L20115763962.9  L20407710113.0  L20594349655.2  L20923585658.2  L20977711877.2  L22406698569.275L22728439456.164L22923672419.264L22923788065.164L22923837191.258L23136739156.1  L23292825792.2  L23657246326.2  L2385600136.1   L24023900370.0  L2487024120.2   L2487147605.2   L25791592377.162L2621559066.1   L26443884051.267L26443884051.269L27111942217.1  L27163688480.4  L27291312838.163L27826531539.1  L27832436220.244L27940405558.8  L28046422800.4  L28316294259.15 L28632618922.2  L29282814771.163L29311549712.259L29311754221.261L29391009772.3  L29974646489.162L30507144274.2  L3055355236.3   L30601243456.2  L30997223346.3  L31145622673.2  L31393302313.268L31393302313.270L31789301242.2  L33594514891.2  L33851503706.2  L34141894720.2  L34522961910.2  L35017493719.2  L35139482716.0  L35497690860.3  L35497693828.3  L35627047303.1  L35666023782.10 L36451390263.2  L37156630869.0  L38107661013.162L38235734261.1  L38259954321.2  L38383890888.1  L38692377683.1  L39231752993.0  L39236637173.0  L39332637397.0  L40170592289.164L40228640085.0  L40585223510.2  L40714693207.6  L41202929119.258L41251426164.1  L41601820452.5  L42248755539.1  L42411609006.0  L42488948659.2  L42894740255.1  L42961455610.14 L43230691980.3  L43301826312.1  L43317676572.3  L43595757740.2  L44166661144.3  L44166924249.3  L44465449044.262L44467498146.162L44467498146.257L44467548957.164L44467548957.259L45653528320.3  L45883208791.2  L46512611463.267L47870616696.2  L47899738467.2  L48117785831.9  L48455046775.1  L48596171480.2  L49233373885.2  L49478371288.2  L4951167123.267 L49526752708.2  L50925318027.2  L51151260616.162L51151260616.257L52610022531.2  L53115519699.1  L53404531630.9  L53505134330.2  L53517063214.257L56459574803.20 L56461361441.10 L56464645271.1  L56499015653.263L56500720864.261L56694929206.269L56694929206.271L56732278231.2  L57130527895.2  L57338894764.3  L57387013391.2  L576250137.258  L57698627611.2  L58039649675.2  L58451383419.10 L58972524609.3  L59308579414.10 L59308586248.2  L59443875285.164L59723830915.2  L59795174902.2  L60098763854.6  L60812373952.10 L61655438821.18 L61655438821.20 L61672228356.263L62371041310.275L62586168108.2  L62831190464.6  L63915962791.1  L64009471222.1  L64148832490.244L64370849402.2  L65762635419.1  L65862516566.2  L66151427842.16 L66298372189.2  L66723443392.2  L66812728480.3  L67070089790.2  L67304579733.2  L67473393319.1  L7725853002.163 L8171953640.244 L881835912.0    L9080220944.4   L9356559676.15  L9619762727.1   L9748633241.2   L9895871740.164 O10644243082.267O10644243082.295O10871149737.267O10871149737.295O1254725598.267 O14075571866.267O14075571866.295O14632083704.267O14912726833.267O14912726833.295O16958666856.295O17217116232.267O17217116232.295O18101220210.295O18988691132.267O18988691132.295O20866770946.267O21298244344.267O21298244344.295O22525005962.295O24222861850.267O24222861850.295O2450246008.267 O2450246008.295 O28973706943.295O30010457231.267O33449646875.267O33449646875.295O33496826488.267O33496826488.295O3493317847.267 O3493317847.295 O37559489567.267O37559489567.295O3821773283.267 O3821773283.295 O44938202843.267O44938202843.295O45637135587.295O4776649498.267 O4776649498.295 O49701823576.267O50809583907.267O52301174499.295O54119978487.267O54119978487.295O56327351971.267O57031441090.267O58364443802.267O63008166051.267O63748625294.295O64474006218.267O64474006218.295O6468225490.295 O6468421667.267 O65961212488.295P11295933877.295P12115299733.274P12115299733.276P19899262166.267P20934313244.267P23298593222.274P23298593222.276P28627113325.274P28627113325.276P30511339222.267P30511339222.295P30586038854.274P30586038854.276P3069564867.267 P3069564867.295 P31146933846.274P31146933846.276P31778598044.267P31778598044.295P33597136077.274P33597136077.276P34157099334.274P34157099334.276P38261788758.274P38261788758.276P38605639612.250P38605639612.274P38605639612.275P42484919333.267P43594459594.295P44164039966.274P44164039966.276P45663739494.295P47876372191.267P47876372191.295P49230739482.267P50927926572.295P51370907562.250P51370907562.274P51370907562.275P53346601986.250P53346601986.274P53346601986.275P53515870108.267P53515870108.295P57140489617.278P57713046236.274P57713046236.276P58041177900.267P58041177900.295P62587740714.278P64359622428.267P64359622428.295P66292560634.267P66292560634.295P66738648006.274P66738648006.276P66818508295.267P66818508295.295P66903681610.250P66903681610.274P66903681610.275P67064334489.267P67064334489.295P7740881908.250 P7740881908.274 P7740881908.275 P9764112383.267 P9764112383.295 Q10002382861.268Q10592533181.267Q10636937134.267Q10636937134.295Q10646134994.267Q10646134994.295Q10649498890.266Q10651751606.265Q10663072064.267Q10665153022.270Q10665496828.274Q10821824020.250Q10821824020.274Q10821824020.275Q10914612381.277Q10916531869.278Q11133374175.267Q11657053839.267Q11938624351.295Q12465444467.234Q12658605510.250Q12658605510.252Q12658605510.274Q12658605510.275Q12658605510.276Q12658605510.277Q13733105547.265Q13846928860.267Q13846928860.295Q13851160440.266Q14360074768.273Q14360074768.275Q14393960896.274Q14394173634.270Q1553561799.270 Q1553906117.274 Q15930096381.270Q15979430805.274Q15979578007.270Q16429527224.267Q16429527224.295Q16627031195.274Q16796962909.240Q17027695041.267Q17027695041.295Q17681074618.267Q17681074618.295Q17701933584.266Q17841111261.247Q18087146764.268Q18087146764.269Q18896927685.274Q18897435335.270Q19561597574.244Q19868621735.295Q19953245935.267Q19953245935.295Q21767670690.267Q21767670690.295Q22726707363.275Q23481527360.270Q23702429453.267Q25887797116.278Q25987188084.268Q27573751300.267Q27573751300.295Q27942454161.267Q27942454161.295Q2803826605.267 Q2803826605.295 Q28465177121.271Q28465177121.273Q28494695274.270Q28494695274.272Q28551846102.274Q28552026580.270Q29775981542.267Q29775981542.295Q30222614424.267Q3054610265.240 Q30926961810.270Q30926978448.274Q31526414380.250Q31526414380.274Q31526414380.275Q3215835802.245 Q32458870384.267Q32681607669.267Q32681607669.295Q32681824661.274Q32681824661.276Q33137450695.267Q33137450695.295Q33283861378.250Q33283861378.274Q33283861378.275Q33306674327.270Q33306723733.274Q34292258162.270Q34292470896.274Q34357517856.244Q34390149656.266Q34669208222.245Q34964695579.243Q35662748640.239Q37149073081.274Q37149073081.276Q38080925904.295Q38105515555.270Q38372880008.242Q38385659317.274Q38385734154.275Q39180574961.274Q39180574961.276Q39600066516.266Q40354196046.250Q40354196046.274Q40354196046.275Q40360481330.235Q41086062499.270Q41086111393.274Q41675861917.238Q4230766280.273 Q4230766280.275 Q42439168719.267Q42439168719.295Q42439443119.274Q42439443119.276Q42439443119.278Q42441548847.250Q42441548847.274Q42441548847.275Q42887926878.241Q43138029699.250Q43138029699.274Q43138029699.275Q43322640365.274Q43322640365.276Q43438798406.274Q43479930840.267Q43479930840.295Q43610412201.267Q43622973458.276Q44298944140.235Q44301027056.250Q44301027056.274Q44301027056.275Q45257319447.274Q45257319447.276Q45317270253.267Q45482765142.252Q45482765142.276Q45482765142.277Q46794843979.267Q46794843979.295Q47799716979.234Q47799716979.268Q47799716979.269Q48118064779.267Q48119910507.250Q48119910507.274Q48119910507.275Q48211510750.267Q50160428632.295Q52314573493.274Q52314950583.270Q5265442331.272 Q5265442331.274 Q53315247896.267Q53666784021.274Q53667029527.270Q54481541668.244Q55415036769.274Q55415036769.276Q5596578838.250 Q5596578838.274 Q5596578838.275 Q56204695986.267Q56204695986.295Q56530976407.267Q56854244147.274Q56854244147.276Q58763128337.270Q59023939651.275Q59099635219.270Q59099635219.272Q59144964087.274Q59144964087.276Q59615732211.268Q59615732211.269Q59865321072.274Q59865321072.276Q59865321072.278Q59865603600.267Q59865603600.295Q59867425008.250Q59867425008.274Q59867425008.275Q60577861380.274Q60952393704.270Q60952442602.274Q61847600945.266Q62190329447.267Q63733638937.238Q64228675114.249Q64228675114.273Q64228675114.274Q64650680438.242Q64655156468.275Q64681563910.250Q64681563910.274Q64681563910.275Q64683667846.274Q64683667846.276Q64683667846.278Q64683942374.267Q64683942374.295Q65150825229.274Q65150825229.276Q65752674778.241Q65752989693.295Q68013150533.274Q68013150533.276Q68043645948.277Q68077445246.268Q68077445246.269Q68519243108.239Q6863764061.243 Q6912043747.247 Q7657268757.274 Q7657711383.270 Q8009443288.295 Q9350530486.244 Q9350530486.272 Q9485152634.250 Q9485152634.274 Q9485152634.275 Q9487243258.278 Q9633850233.244 Q9644583048.267 Q9644583048.295 Q97189773.270   Q97336975.274   00000Z01D01n02j04U06a08=09Y09Z0:V0;@0=a0?O0@90@c0Af0BW0CH0Ec0GK0H50H_0J10Jn0L=0MK0N]0Om0Q80RI0SX0Tf0V50V\0WC0XR0Yb0[40\?0]P0^M0_]0`V0af0bc0d30eE0fB0gQ0h_0j00k?0lM0li0lj0lk0mS0mT0mY0mZ0mf0nT0ni0nj10l11;11>11C11D11E11F12Q13\13o14Y15C16416E16F16G16H16i16j16k16l16m16n17m19C1:R1;h1;m1;n1;o1<41<51<61<71=W1=\1>F1?01?41?D1?n1@31@]1A21AA1Ad1Ae1BK1BL1BM1BN1BO1BP1BQ1BR1BS1BT1C>1Ch1Ci1Cj1D41D51D61D71D81D91D:1DA1DW1DX1DY1F11F51F61F;1F@1FA1FB1FC1Fk1Fl1Fm1GC1Gm1H11HC1HH1HI1HJ1HO1I71IC1IG1IR1IS1IT1IU1KR1MA1O>1Pm1Rj1Rk1Rl1SV1SW1S_1T?1TC1TD1TE1TM1U71U81U91Vo1Y31Y41Y91YZ1Y[1ZE1ZU1[21[31\i1^_1_I1`31`41`51`61`=1`g1`h1`i1a:1aF1aW1a]1b\1b]1b^1bh1cE1ch1dK1dL1dM1dN1df1dk1dl1f61f71f<1f=1fh1fi1fj1fk1fl1fm1g21g\1g]1g^1gm1hR1hW1hX1j01j11j21j31j41j51j61j71j81j91j:1j;1j<1j=1j>1j?1j@1jA1jB1jC1jD1jE1jF1jG1jH1jI1jJ1jK1jL1jM1jN1jO1jP1jQ1jR1jS1jT1jU1jV1jW1jX1jY1jZ1j[1j\1j]1j^1j_1j`1ja1jb1jc1jd1je1jf1jg1jh1kf1nJ20U21a23<25G26_2902:N2;i2=j2@52AM2C02E92GJ2Hh2JC2L?2NJ2Ob2Qm2SE2UV2W42X32Y22Z12[52\;2]52^22_82`D2aP2b\2ch2dh2eh2fh2h?2jL2kc2m>2o:30J31@32933Z35\37438O3:K3;23;Y3=d3?<3@X3B43Bo3Cj3De3FH3HQ3IL3JG3KB3L]3NY3O<3O^3P=3P\3P]3P^3Q=3Q\3S:3TX3V63W13Wl3Xg3Y\3ZQ3[33[43[W3\93]43^E3_@3`;3aL3b]3c<3c=3c>3c?3d13df3dg3dh3di3dj3eI3eJ3eK3fQ3gW3iA3j63jU3k43lW3n`3o?40040R41441541642P43343443544P46L47R48448548j49M49N49O4:b4<V4=94=\4>G4?24?U4@84@94@:4@a4AH4Aj4B_4B`4Ba4Bb4Bc4Bd4CU4D74D84D94D:4D;4De4EO4EP4EQ4ER4ES4ET4EU4EV4FJ4FK4G<4Ha4IV4L:4NE4Nh4P64Pk4QN4R14T<4UT4UU4VL4WC4X:4X_4X`4Xa4YV4ZH4[=4[e4\M4]H4^F4_D4`D4aD4bD4c94c:4c;4c<4c=4c>4ca4eD4gM4gl4hX4i=4j44jk4kb4nF50Q50R51c53454E54d55C55e56G56i57g59=5;I5<_5>I5>J5>K5>L5?85?d5?e5?f5?g5@o5Ae5B^5B_5B`5Ba5Bb5Bc5Bd5Be5Bf5DP5E;5E^5FA5HL5Id5Ie5If5Ig5Ih5Ii5Ij5Ik5Il5Im5In5JQ5JR5JS5KT5L65Lk5NZ5Q05Re5SZ5T=5Uj5XA5ZD5\V5^W5`c5b85cn5co5d05de5eH5h=5jV5kK5km5lO5mD5n@5o15o25o35oV60>60f61a62\63W64O65465Y66>66?66@S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS2FB3sp13cur3SP13SPR2F04CPOS4SP1RS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS2p02es2FB3sp13cur3SP13Hp13Hp33SPR2F04CPOS4SP1R2q13L1w3Hq13HqL3KL0S1R3HIA1h2LF2sp2PP1P3END3CUR1d2bs3LFB3PP02B24CUR03TOP2FB3sp13cur2hc3HTc3SP13SPR2F04CPOS4SP1RS1R3HIA1h2LF2sp2PP1P3END3CUR1d2bs3LFB3PP02B24CUR03TOP2FB3sp13cur2hc3HTc3SP13SPR2F04CPOS4SP1RFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13TOP2p02es2FB3sp13cur2hc3HTc3SP13Hp13Hp33SPR2F04CPOS4SP1R2q13L1w3Hq13HqL2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3CUR1d2bs3LFB3PP02B24CUR03TOP2FB3sp13cur2hc3HTc3SP12rv3SPR2F04CPOS4SP1R2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13cur2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13curS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13curS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3LOS2p02es2FB3sp13cur3SP13Hp13Hp33SPR2F04CPOS4SP1R2q13L1w3Hq13HqL2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13cur3SP12rv3SPR2F04CPOS4SP1R2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur3x294CFBa2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2ob4CFBa2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur3x293CPP2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur3x294CFBa2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x144CFBa2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13x143APP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur3x293APP2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur3x293CPP2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB2p02es2FB3sp13x143APB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3DPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3DPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x144CFBa2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur3x294CFBa2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13x143APP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur3x293APP2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3cur3CBF2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x144CFBa2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2ob3CPP2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x144CFBa2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2ob4CFBa2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x144CFBa2x23x153x163x174POSTS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3sp13cur3x293CBF2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2ob4CFBa2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur3x293CPP2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur3x293APP2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur3x293CPP2q13L1w3x173x303x313x324POSTS1P3BUF2B12p02es3Hp12q14Hq1rFFS1R2sp3BUF2lo2bs3SLO3LOS3sp13SP13ALO3BCEFS3CURFS2q13L1w3LR1S1R2sp2PP1P3END3CUR1d2bs2FB3sp13cur2q13L1w3LR1S1P3END2p02es3Hp23Hp3FS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12p02es2FB3sp13cur3Hp13Hp33SPR2F04CPOS4SP1R2q13L1w4Hq1r3Hq13HqL3KL0S3BUF2bs2FB3APBS1lS3curFFSS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2HB5Ha_st5Hl_st5SAEst5CM8st2x22HxS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2HB5Ha_st5Hl_st5SAEst5CM8st2x22HxS2p02q13L1w3Hq13KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3sp13cur2q1S1P3BUF2B12p03Hp1FFFS1P2p02es3Hp12q13L1w4Hq1r2q24Hq2rSFFFFS1R2sp2PP1P3END3CUR1d2bs3PP02B22FB3sp13cur3SPR2F03CAL4CPOS4SP1RS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3SPH2FB3sp13cur3SPR2F04CPOS3CLO4SP1RS1R2sp2PP1P3END3CUR2lo1d2bs3PP02B24CUR03SLO3SPH2FB3sp13cur3SPR2F04CPOS3CLO4SP1RS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3SPH2FB3sp13cur3SPR2F04CPOS3CLO4SP1RS3curFFS3curSFSS1R2sp2PP1P3END3BUF3CUR1d2bs3PP02B12B22B54CUR02p02FB3sp13cur3Hp13SPR2F04CPOS4SP1R2q13L1w3LR13Hq1S3sp1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS2PPS3BUF2bs3cur3CBFS1R2sp2PP1P3END3CUR1d2bs2FB3sp13cur2rv3HrvS3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2sp2lo3SLO3sp13SP1S2es2q13L1w3HqLS1R2sp2lo3SLO3LOS2FB3sp13SP13ALO2F1FS1R2sp2PP1P3END3CUR1d2bs2FB3sp13cur2rvFFFFFFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFFS3cur4CPOSFFFSSSS5nodesS1R3HIA1h2sp2lo3TOP2HTFSS1R2sp2PP1P3END3BUF3CUR1d2bs3PP02B12B22B54CUR02p02FB3sp13cur3Hp13SPR2F04CPOS4SP1R2q13Hq1S2loFS3curS3curSSSS1R2sp2PP1P3END3CUR1d2bs2FB3sp13cur4CPOSSFS3END3BUF2bs2B32es3Hp3S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS2FBS2p02q13Hq12q23HqOS3curSFS3curS1R2sp3BUF2lo2bs3SLO3LOS3sp13SP12BL4ALOrS2PP3cur3CPPS2FBS2PP2FB3APPFFFS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B32B53DPB4CUR02D12p02es2FB3sp13cur3Hp13Hp33ACV3SPR2F04CPOS4SP1R3BCE2q14Hq1r3Hq1S1R2sp2PP1P3END3BUF3CUR1d2bs3PP02B12B22B32B54CUR02p02es2FB3sp13cur3Hp13Hp33ACV3SPR2F04CPOS4SP1R3BCE2q14Hq1r3Hq1S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B32B53DPB4CUR02D12p02es2FB3sp13cur3Hp13Hp33ACV3SPR2F04CPOS4SP1R3BCE2q14Hq1r3Hq1S1R2sp2PP1P3END3BUF3CUR1d2bs3PP02B12B22B32B54CUR02p02es2FB3sp13cur3Hp13Hp33ACV3SPR2F04CPOS4SP1R3BCE2q14Hq1r3Hq1S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B32B53DPB4CUR02D12p02es2FB3sp13cur3Hp13Hp33ACV3SPR2F04CPOS4SP1R3BCE2q14Hq1r3Hq1FFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFS2rv3HrvS1R2sp2lo3slo4SLOS4SLOL3SLO4ALOxS2FBFFS2sp3sp1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFFS1R2sp2PP1P3END3BUF3CUR1d2bs3PP02B12B22B32B54CUR02p02es2FB3sp13cur3Hp13Hp33ACV3SPR2F04CPOS4SP1R3BCE2q13L1w3LR13Hq13HqLS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B32B53DPB4CUR02D12p02es2FB3sp13cur3Hp13Hp33ACV3SPR2F04CPOS4SP1R3BCE2q13L1w3LR13Hq13HqLFS3curS3END3BUF2bs2B32es3Hp32q13L1w3HqLFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1P3END1d2rv3HrvS1R2sp2lo3SLO3sp13cur3SP13CLOFS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12p02es2FB3sp13cur3Hp13Hp33SPR2F04CPOS4SP1R2q14Hq1r3Hq1S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12p02es2FB3sp13cur3Hp13Hp33SPR2F04CPOS4SP1R2q14Hq1r3Hq1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFFFS2FB2F0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFFS2rv3Hrv1r2Kr1q1HS3BUF2bs3B47S2rv3Hrv1r2KZ1q1HS1i2HiS1R2sp2PP1P3END3CUR1d2bs3PP02B22FB3sp13cur3SPR2F03CAL4CPOS4SP1RFFS1R2lo3LOSS1R2sp2PP2lo4PPLO3SLO3sp13SP1S1P3END1d2p02es3Hp13Hp23Hp32q14Hq1rS1P3END1d2p02es3Hp13Hp23Hp32q14Hq1rFFFS1P3END2p05nodes3CNT3KNBS3curFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxFS3curFS2FB2r03F641q1r1H2H02q02H43sp14SP1M3cur3CALFFFFFS3curS1R2sp2PP1P3END3CUR1d2bs2FB3sp13cur2rv3HrvFSS2sp2lo3sp13SP1S1R2sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS3curFS1R2sp2PP1P3END3BUF3CUR1d2bs3PP02B12B22B54CUR02p02FB3sp13cur3Hp13SPR2F04CPOS4SP1R2q13Hq1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3cur3SPR3CLOS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B303DPB4CUR05CURLO3DCB3SLO3LOS2p02es3sp13SP13Hp13Hp33ALO3SPR3BCE2q13L1w4Hq1r3LR13Hq13HqL3BLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS2p02es3sp13SP12rv3Hp13Hp33ALO3SPR3BCE2q14Hq1r2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO2p02es3sp13cur3SP13Hp13Hp33SPR3CLO2q13L1w3Hq13HqL2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP12rv3SPR3CLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3LOS2p02es2FB3sp13SP13Hp13Hp33ALO3SPR2F12q13L1w3Hq13HqL2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP12rv3ALO3SPR2F12HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3ALO3SPR3BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS2p02es3Hp13Hp33ALO3SPR3BCE2q13L1w4Hq1r3Hq13HqL3KL0S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO2p02es3sp13cur3SP13Hp13Hp33SPR3CLO2q13L1w3Hq13HqL2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP12rv3SPR3CLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS2p02es3sp13SP13Hp13Hp33ALO3SPR3BCE2q13L1w4Hq1r3Hq13HqL3KL0S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3LOS2p02es2FB3sp13SP13Hp13Hp33ALO3SPR2F12q13L1w3Hq13HqL2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP12rv3ALO3SPR2F12HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2p02es3sp13cur3SP13Hp13Hp33SPR3CLO2q13L1w3Hq13HqL3KL0S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO2p02es3sp13cur3SP13Hp13Hp33SPR3CLO2q13L1w3Hq13HqL2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP12rv3SPR3CLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO2p02es3sp13cur3SP13Hp13Hp33SPR3CLO2q13L1w3Hq13HqL2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP12rv3SPR3CLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3LOS2p02es2FB3sp13SP13Hp13Hp33ALO3SPR2F12q13L1w3Hq13HqL2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP12rv3ALO3SPR2F12HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3APB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3APB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3APB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3ALO3SPR2F1S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3sp13BLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3sp12rv3BLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4CFBa2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4CFBa2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4CFBa2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB3PP02B24CUR04SLOS2FB3ALO3SPR2F12HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D14SLOS2p02es2FB3Hp13Hp33ALO3SPR2F12q13L1w3Hq13HqL2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB3PP02B24CUR04SLOS2FB3ALO3SPR2F12HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2p02es3sp13cur3SP13Hp13Hp33SPR3CLO2q13L1w3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3cur2ob3SPR3CLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP12HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP12rv2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS2p02es2FB3sp13SP13Hp13Hp33ALO3SPR2F12q13L1w3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP12ob3SPR3CLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2p02es3sp13cur3SP13Hp13Hp33SPR3CLO2q13L1w3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP1S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO2p02es3sp13cur3SP13Hp13Hp33SPR3CLO2q13L1w3Hq13HqL2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP12rv3SPR3CLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B24CUR05CURLO2D13SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B24CUR05CURLO2D13SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APC2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APC2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APC2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS2p02es3sp13SP13Hp13Hp33ALO3SPR3BCE2q13L1w4Hq1r3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APP2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APP2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APP2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2p02es3sp13cur3SP13Hp13Hp33SPR3CLO2q13L1w3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR1d2bs3LFBFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12p02es3Hp13Hp33SPR2q14Hq1r3Hq1S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12p02es3Hp13Hp33SPR2q14Hq1r3Hq1S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12p02es3Hp13Hp33SPR2q14Hq1r3Hq1S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3BCE2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3BCE2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3BCE2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFBFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp12HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp12rv2HB5Ha_st5Hl_stFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFBFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12p02es3Hp13Hp33SPR2q13L1w4Hq1r3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS2p02es3sp13SP13Hp13Hp33ALO3SPR3BCE2q13L1w4Hq1r3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBFFS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3F643SPR2F04CPOS4SP1RS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curFFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS3sp13SP13ALO3SPRS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS2p02es3sp13SP13Hp13Hp33ALO3SPR2q13L1w3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3PP02B22FB3sp13cur3SPR2F03CAL4CPOS4SP1RS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2q1FS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp1FFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13SP13SPRS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2p02es3sp13SP13Hp13Hp33SPR2q13L1w3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp14SP1R2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp14SP1R2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp1FFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stFFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBFFFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP1S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP1FFFFFFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB2HB5Ha_st5Hl_stFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2FB3sp13SP13SPR2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B303DPB4CUR05CURLO3DCB3SLO3LOS2p02es3sp13SP13Hp13Hp33ALO3SPR3BCE2q13L1w4Hq1r3LR13Hq13HqL3BLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS2p02es3sp12rv3SP13Hp13Hp33ALO3SPR3BCE2q14Hq1r2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B53DPB4CUR02D12p03Hp13SPR2q13Hq1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3LOS2p02es3sp13SP13Hp13Hp33ALO3SPR2q13L1w3Hq13HqL2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS3sp12rv3SP13ALO3SPR2HB5Ha_st5Hl_stFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HBFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp12HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp12rv2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOSS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOSS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS3sp12HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS3sp12rv2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS3cur2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stFFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33DPB4CUR05CURLO3SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33DPB4CUR05CURLO3SLO3LOS2p02es3sp13SP13Hp13Hp33ALO3SPR3BCE2q13L1w4Hq1r3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2HB5Ha_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B303DPB4CUR05CURLO3DCB3SLO3LOS2p02es3sp13SP13Hp13Hp33ALO3SPR3BCE2q13L1w4Hq1r3LR13Hq13HqL3BLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33DPB4CUR05CURLO3SLO3LOS2p02es3sp12rv3SP13Hp13Hp33ALO3SPR3BCE2q14Hq1r2HB5Ha_st5Hl_stFS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3BCE2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3BCE2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3BCE2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS3ALO3SPRS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3ALO3SPR2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3LOS2p02es2FB3Hp13Hp33ALO3SPR2q13L1w3Hq13HqL2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3ALO3SPR2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12p02es3Hp13Hp33SPR2q13L1w4Hq1r3Hq13HqL3KL0FFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp12HB5Ha_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp12HB5Ha_stFFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO2FB3SPR2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP12HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp12rv3SP12HB5Ha_st5Hl_stFFFFFFFFS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12p02es3Hp13Hp33SPR2q13L1w4Hq1r3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4CPOS2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp1S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO2p02es3sp13cur3SP13Hp13Hp33SPR3CLO2q13L1w3Hq13HqL2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur2rv3SP13SPR3CLO2HB5Ha_st5Hl_stFFFFFFFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3ALP3PP02B22FB3sp13cur3SPR2F04SP1RS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3F643SPR2F04CPOS4SP1R2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D12p02es2FB3sp13cur3F643Hp13Hp33SPR2F04CPOS4SP1R2q13L1w3Hq13HqL2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13cur3F643SPR2F04CPOS4SP1R2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP2FB3SPR2HT2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13TOP2p02es2FB3Hp13Hp33SPR2HT2q13L1w4Hq1r3LR13Hq13HqL2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP2p02es2FB3Hp13Hp33SPR2HT2q14Hq1r2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13TOP2p02es3sp13Hp13Hp33SPR2HT2q13L1w4Hq1r3LR13Hq13HqL2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP2p02es3sp12rv3Hp13Hp33SPR2HT2q14Hq1r2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP2p02es3cur2ob3Hp13Hp33SPR2HT2q13L1w3Hq13HqL3KL02HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP3SPR2HTS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP2p02es3Hp13Hp33SPR2HT2q13L1w3Hq13HqL3KL0FFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33B303DPB4CUR05CURLO3DCB2D13SLO3LOS2p02es2FB3sp13cur3SP13Hp13Hp33ALO3SPR2F13CLO3BCE2q13L1w4Hq1r3LR13Hq13HqL3BLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS2p02es2FB3sp13cur2rv3SP13Hp13Hp33ALO3SPR2F13CLO3BCE2q14Hq1r2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13SP12HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_stFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp14SP1RS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp14SP1RS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2F0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2F0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2F0FF". (* [comment removed for export] *)
  #[using="IMG CALLOC GETTAG FREEL LFB ALP PP0 CWP PPLO HBY BIN B1 B2 B3 B47 B5 B30 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS err_exit' l2_walk'"] Lemma inner_walk : forall p0 es,
    (forall p' es', p0 < p' -> InnerOb p' es') -> (forall p', p0 < p' -> OuterOb p') -> InnerOb p0 es.
  Proof.
    intros p0 es KIN KOUT. unfold A_x509_get_name_E.InnerOb.
    intros FB sp1 w0 w1 w2 ga gb b4 j0 j96 nodes cur PHIx FFRx mc moc hc jo olen j1 vlen j2 mg' p7 xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s6v
           D W0 W1 W2 W3 W4 PPc Hp1 Hp2 Hp3 CNT PHI FFR BUD BUDF UW.
    pose proof D as D0. nvA_open D. rt_facts. walk_prep. cur_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NRT; lia).
    assert (NN : 0 <= Z.of_nat (length nodes)) by (clear; lia).
    assert (KD : Z.of_nat (length nodes) <= NB / 6) by (assert (KNB : p0 - P <= NB) by (clear - Hp2 Hp3; lia); apply Z.div_le_lower_bound; [clear; lia| clear - CNT KNB; lia]).
    pose proof (blocks_below_hm R HIA hc _ _ mc _ HHc ltac:(intros b Hb; exact Hb)) as BBc.
    destruct (BBc (BUF, n) ltac:(apply SUBL; exact BIN)) as [_ BCE]. cbn [fst snd] in BCE. clear BBc.
    (* [comment removed for export] *)
    lazymatch type of HHc with HM _ _ _ _ ?LBh ?LFh _ =>
      assert (INHq : @In blk (FB, 24) (@app blk LBh (fdata LFh))) by (apply in_or_app; right; cbn; left; reflexivity);
      assert (INDq : @In blk (FB + 32, 128 - 40) (@app blk LBh (fdata LFh))) by (apply in_or_app; right; cbn; right; left; reflexivity)
    end.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    start_Wf cur FB.
    (* [comment removed for export] *)
    zstep.
    wsyncf.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HH) as ABc end end.
    frame_aobj FSH (FB + 32) 1%nat as OGA.
    pose proof GETTAG as GT'. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG_G in GT'.
    pose proof (conj PPc (conj GA (conj STlo I))) as CBOX. clear PPc GA STlo.
    acallxA_sp_keep sp1 MUk WMk
      (eapply GT' with (CS := hcs asegs R HIA hc) (PP := PP) (LENP := FB + 32) (P := p0) (END := es) (BUF := BUF) (bs := bs) (tag := 48) (lo := lo) (lenv := ga);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ gt_side CBOX OGA ABc BCE
               | lazymatch goal with
                 | |- BUF <= p0 => clear - B1 Hp1; lia
                 | |- p0 <= es => exact Hp2
                 | |- es <= BUF + _ => clear - Hp3 B3; lia
                 | |- PP + 8 <= FB + 32 \/ _ => clear - APP; lia
                 | |- _ = 0 \/ FB + 32 + 8 <= BUF \/ _ => right; clear - APB; lia
                 | |- (FB + 32) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                 | |- 0 < FB + 32 => clear - F0; lia
                 | |- FB + 32 + 8 <= sp1 - 16 \/ _ => left; clear - F1 ALO LOS SLO SP1 NS1 NRT; unfold A_x509_get_name_A.STKn in SLO; lia
                 end
               | match goal with |- ?g => idtac "GT1-PRE-LEFT:" g end ]).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "GT1-LEFT:" g end.
    clear ABc OGA CBOX.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rv end.
    match goal with H : _ < rv <= 0 |- _ => rename H into Hrv end.
    match goal with H : rv = 0 -> _ |- _ => rename H into HL0 end.
    match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into PPc; rename qq into q1 end.
    match goal with H : rw_cells _ _ (FB + 32) [C8 ?lw] |- _ => rename H into GA; rename lw into L1w end.
    match goal with H : p0 <= q1 <= es |- _ => rename H into Hq1r end.
    pose proof (bv_unsigned_in_range 64 L1w) as LR1. unfold bv_modulus in LR1. cbn [Z.pow Z.of_N Pos.pow] in LR1.
    gt_sync MUk WMk cur sp1 FB (FB + 32).
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr.
    2: { (* [comment removed for export] *)
      start_Wf cur FB.
      do 3 (step; zsimp).
      rewrite (swrap32_land_errsum rv 18446744073709542528) by (clear - Hrv; lia).
      zpre.
      zstep.
      zstep. if_cases KZ; zify_cond KZ.
      - wsyncf. start_Wsf cur (sp1 + 72) FB. blo sp1 SP1. zstep. wsyncsf. go_err W0 W1 W2 W3 W4 ltac:(clear - PHI FFR CNT KD Hp1 Hp2 Hp3 NN Hq1r Hrv).
      - exfalso. clear - KZ Hrv. change 18446744073709551615 with (Z.ones 64) in KZ. rewrite Z.land_ones in KZ by lia. Z.div_mod_to_equations. lia. }
    assert (R0 : rv = 0) by (clear - Kr Hrv; change 18446744073709551615 with (Z.ones 64) in Kr; rewrite Z.land_ones in Kr by lia; Z.div_mod_to_equations; lia).
    subst rv. destruct (HL0 eq_refl) as [Hq1 HqL]. clear HL0 Kr Hrv.
    (* [comment removed for export] *)
    zpre.
    if_cases KL; zify_cond KL.
    { (* [comment removed for export] *)
      start_Wf cur FB.
      zstep. zstep. zstep.
      wsyncf. start_Wsf cur (sp1 + 72) FB. blo sp1 SP1. zstep. wsyncsf. go_err W0 W1 W2 W3 W4 ltac:(clear - PHI FFR CNT KD Hp1 Hp2 Hp3 NN Hq1r). }
    (* [comment removed for export] *)
    zpre.
    shadow_chk OBUF q1 1.
    (* [comment removed for export] *)
    get_byte bs (q1 - BUF) ob NBo. read_at BYc NBo (q1 - BUF) RDo.
    zpre.
    start_Wf cur FB. zstep.
    try clear RDo.
    (* [comment removed for export] *)
    zstep. zstep.
    wsyncf.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HH) as ABc end end.
    lazymatch goal with OC : aobj _ _ _ ?mx cur 64 |- context [MS _ _ _ _ _ ?mx _] =>
      assert (OLEN : aobj asegs AL (hcs asegs R HIA hc) mx (cur + 8) 8) by (eapply aobj_sub; [exact OC| clear; lia| clear; lia]) end.
    lazymatch goal with SL : stk _ _ lo sp1 |- _ => pose proof (conj PPc (conj W1 (conj SL I))) as CBOX; clear PPc W1 SL end.
    acallxA_sp_keep sp1 MUk WMk
      (eapply GT' with (CS := hcs asegs R HIA hc) (PP := PP) (LENP := cur + 8) (P := q1) (END := q1 + bv_unsigned L1w) (BUF := BUF) (bs := bs) (tag := 6) (lo := lo) (lenv := olen);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ gt_side CBOX OLEN ABc BCE
               | lazymatch goal with
                 | |- BUF <= q1 => clear - B1 Hp1 Hq1r; lia
                 | |- q1 <= q1 + _ => clear - LR1; lia
                 | |- q1 + _ <= BUF + _ => clear - HqL Hp3 B3; lia
                 | |- PP + 8 <= cur + 8 \/ _ => clear - CPP; lia
                 | |- _ = 0 \/ cur + 8 + 8 <= BUF \/ _ => right; clear - CBF; lia
                 | |- (cur + 8) mod 8 = 0 => clear - CAL; Z.div_mod_to_equations; lia
                 | |- 0 < cur + 8 => clear - CPOS; lia
                 | |- cur + 8 + 8 <= sp1 - 16 \/ _ => left; clear - CLO SLO SP1 NS1 NRT; unfold A_x509_get_name_A.STKn in SLO; lia
                 end
               | match goal with |- ?g => idtac "GT2-PRE-LEFT:" g end ]).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "GT2-LEFT:" g end.
    clear ABc OLEN GT' CBOX.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rv end.
    match goal with H : _ < rv <= 0 |- _ => rename H into Hrv end.
    match goal with H : rv = 0 -> _ |- _ => rename H into HL0 end.
    match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into PPc; rename qq into q2 end.
    match goal with H : rw_cells _ _ (cur + 8) [C8 ?lw] |- _ => rename H into W1; rename lw into OLw end.
    match goal with H : q1 <= q2 <= _ |- _ => rename H into Hq2r end.
    gt_sync MUk WMk cur sp1 FB (cur + 8).
    nvA_rebuild D3.
    intros moq [HKq MFq].
    eapply l2_walk' with (p0 := p0) (es := es);
      first [ eapply nvA_mo; [exact D3| exact HKq| exact MFq] | exact W0 | exact W1 | exact W2 | exact W3 | exact W4 | exact PPc | exact Hrv | exact Hp3
            | exact CNT | exact PHI | exact FFR | exact BUD | exact BUDF | exact UW | exact KIN | exact KOUT
            | lazymatch goal with
              | |- P <= q2 => clear - Hp1 Hq1r Hq2r; lia
              | |- q2 <= _ => exact (proj2 Hq2r)
              | |- rv = 0 -> p0 + 4 <= _ => intros E0; pose proof (proj1 (HL0 E0)) as HqO; clear - HqO Hq1; lia
              | |- rv = 0 -> _ => intros E0; exact (proj2 (HL0 E0))
              | |- p0 < _ => clear - Hq1 KL0; lia
              | |- _ <= es => clear - HqL; lia
              | |- P <= p0 => exact Hp1
              end
            | match goal with |- ?g => idtac "IN-L2-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03m0@D10636937134.252D16071854214.252D16901939902.252D3953997537.258 D46113380110.252D46794843979.252D56536395888.252D5984197035.252 D60109446735.252D60189065437.258K10558392113.252K1932217360.252 K20981739667.252K23672143632.252K2870125178.252 K30993319891.252K3270517425.252 K32782467746.252K34516387472.252K35852068145.252K59810587792.252K65858155712.252K67298046963.252K68434149297.252L10564965975.2  L11431517604.16 L11949961375.1  L1212436508.3   L12126572370.2  L12730738952.1  L12811117941.3  L12811187658.157L12950669463.6  L13199424678.4  L16641873078.1  L1685717371.0   L18023395959.1  L1848725797.251 L18549529655.5  L1942461814.2   L20923585658.2  L20977711877.2  L21065699441.3  L23292825792.2  L23657246326.2  L2487147605.2   L2621559066.1   L26443884051.252L27111942217.1  L27289337253.160L27940405558.8  L28632618922.2  L2883004908.3   L29280834640.160L29311549712.243L30507144274.2  L3055355236.3   L30601243456.2  L30997223346.3  L31145622673.2  L31393302313.253L31789301242.2  L3256677335.2   L32766956484.2  L33312313103.2  L33594514891.2  L34141894720.2  L34522961910.2  L34680000318.5  L35497690860.3  L35627047303.1  L35666023782.10 L35838227543.2  L3647304025.157 L37156630869.0  L38107661013.157L38235734261.1  L38259954321.2  L38383890888.1  L39036898081.0  L39236637173.0  L39332637397.0  L40228640085.0  L41202929119.242L41663468825.242L42961455610.14 L44166924249.3  L44467498146.157L44467498146.241L47870616696.2  L47899738467.2  L48117785831.9  L49478371288.2  L50925318027.2  L51151260616.157L51151260616.241L52293817109.4  L53505134330.2  L53517063214.241L53527181501.2  L54379384959.7  L5637578809.157 L56694502969.254L57698627611.2  L58451383419.10 L58972524609.3  L59308586248.2  L59795174902.2  L60098763854.6  L60448817524.1  L60812373952.10 L61004000883.15 L61640928013.19 L62035594119.1  L62037170155.19 L62520191992.2  L62831190464.6  L64370849402.2  L64526681523.2  L65862516566.2  L66151427842.16 L66298372189.2  L66723443392.2  L66812728480.3  L66925259772.229L67070089790.2  L67304579733.2  L68418727639.2  L7723644457.160 L8365027124.4   L881835912.0    L9080220944.4   L9356559676.15  L9748633241.2   O10871149737.252O14075571866.252O14632083704.252O14912726833.252O18664807618.252O18988691132.252O20098837283.252O21298244344.252O22525005962.252O24222861850.252O2450246008.252 O3078286936.252 O32263864995.252O33083286018.252O33449646875.252O33496826488.252O3493317847.252 O37559489567.252O3821773283.252 O38925841571.252O44938202843.252O4776649498.252 O54119978487.252O57791108643.252O58364443802.252O64474006218.252O65961212488.252O67171060367.252O8121201118.252 P12115299733.258P20934313244.252P21063123670.252P23298593222.258P28627113325.258P30511339222.252P30586038854.258P3069564867.252 P31146933846.258P31778598044.252P33597136077.258P34157099334.258P38261788758.258P44164039966.258P47876372191.252P50927926572.252P53515870108.252P53529750042.252P57713046236.258P64359622428.252P64538971685.252P66292560634.252P66738648006.258P66818508295.252P67064334489.252P9764112383.252 Q10636937134.252Q10646134994.252Q10649498890.250Q10651751606.249Q13733105547.249Q13846928860.252Q13851160440.250Q16429527224.252Q17027695041.252Q17681074618.252Q17701933584.250Q19405264404.254Q19561597574.229Q21254955245.252Q21767670690.252Q27573751300.252Q27942454161.252Q2803826605.252 Q28465177121.255Q29775981542.252Q32437204119.252Q32681607669.252Q32681824661.258Q33137450695.252Q3421936230.257 Q34390149656.250Q34669522109.252Q34671230885.249Q34671339340.229Q35333735439.229Q37149073081.258Q39180574961.258Q39600066516.250Q41261985556.249Q41414298335.252Q42439168719.252Q42439443119.258Q43322640365.258Q43479930840.252Q45257319447.258Q46794843979.252Q47780987149.252Q48118064779.252Q51218566552.252Q5265442331.256 Q53876796809.254Q55202259380.249Q55415036769.258Q56204695986.252Q56854244147.258Q57228775306.257Q59144964087.258Q59865321072.258Q59865603600.252Q61847600945.250Q64683667846.258Q64683942374.252Q65150825229.258Q68013150533.258Q7368715401.249 Q8126701711.252 Q9350530486.229 Q9633850233.229 Q9644583048.252 00000Z02E03a05O06906c07M07N08?09g0;40<@0=H0>T0?`0@G0AT0Ba0Cm0E:0FF0GN0HZ0Ig0Ih0JP0JU0J`0Ja0Je0K10K_0L50LC0LH0LI0LM0M70MH0MI0MJ0MK0ML0MM0MN0MO0MT0N>0NB0Nl0OA0OB0OC0Oi0Oj0Ok0Ol0Om0On0Oo0PY0PZ0P[0P\0Pc0Pd0Pe0Pf0Q80Q90Q@0QV0QW0QX0QY0S10S50S60S;0S<0S=0S>0S?0Si0TS0U;0U<0Vd0XZ0X[0Xc0YC0YK0YL0[;0]80]H0]I0^30^40^P0`00`Z0`[0`l0a80a>0a?0aI0aM0aj0bM0bi0bj0c:0c;0cS0cT0cU0cV0d90d:0d;0d<0df0dg0dh0di0eS0eb0ec0f20fW0fX0fY0fZ0f[0f\0f]0f^0f_0f`0fa0fb0fc0fd0fe0ff0fg0fh0fi0fj0fk0fl0fm0fn0fo0g00g10g20g30g40g50i50jP0k\0m40nR0oS10k12>13\15716O17g19E1:B1;N1<Z1>51?A1@:1AU1BY1C@1DX1F41GW1I21IQ1IR1J11JP1Jo1K01K11L71LV1N91NX1OV1Q01Q11RL1RM1S`1TC1Tn1UU1UV1UW1UX1VB1W>1W?1Wa1XC1Xe1YG1[G1\_1\`1]J1]l1^T1_R1_S1a61c61cU1cV1dT1e61eb1fL1fn1gg1gh1gi1i91jQ1jR1jS1kT1mJ1n_1n`20n21l21m22U23:23_S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS2FB3sp13cur3SP13SPR2F04CPOS4SP1RS1R3HIA1h2LF2sp2PP1P3END3CUR1d2bs3LFB3PP02B24CUR03TOP2FB3sp13cur2hc3HTc3SP13SPR2F04CPOS4SP1RS1R3HIA1h2LF2sp2PP1P3END3CUR1d2bs3LFB3PP02B24CUR03TOP2FB3sp13cur2hc3HTc3SP12rv3SPR2F04CPOS4SP1R2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13curS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13cur3SP12rv3SPR2F04CPOS4SP1R2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x144CFBa2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13x143APP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB2p02FB3sp13x143APB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3DPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x144CFBa2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x144CFBa2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x144CFBa2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13x143APP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x144CFBa2x23x153x163x174POSTFS1R2sp3BUF2lo2bs3SLO3LOS3sp13SP13ALO3BCES3CURS2PP2FB3APPFS2FBS2q13SLw3LR1S1R2sp2PP1P3END3CUR1d2bs2FB3sp13cur2q13SLw3LR1S1P3END2p03Hp12q14Hq1rS1P3END2p03Hp2S3curSS2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1P3BUF2B12p03Hp1FFFFFFSS3sp1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS2PPS1R2sp2PP1P3END3CUR1d2bs2FB3sp13cur2rv3HrvS1R2sp2lo3SLO3sp13SP1FFS1R2sp2PP1P3END3CUR1d2bs2FB3sp13cur2rvFFFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFFFS2FB2F0FFFS2p02q13Hq12p'3Hp'SS5nodesS1R3HIA1h2sp2lo3TOP2HTFFSS1R2sp2PP1P3END3BUF3CUR1d2bs3PP02B12B22B54CUR02p02FB3sp13cur3Hp13SPR2F04CPOS4SP1R2q13Hq1S2loFS3curSSSSS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2sp3BUF2lo2bs3SLO3LOS3sp13SP12BL4ALOrFS1R2sp2PP1P3END3BUF3CUR1d2bs3PP02B12B22B32B54CUR02p02FB3sp13cur3Hp13ACV3SPR2F04CPOS4SP1R3BCE2q14Hq1r3Hq1S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B32B53DPB4CUR02D12p02FB3sp13cur3Hp13ACV3SPR2F04CPOS4SP1R3BCE2q14Hq1r3Hq1FS2rv3HrvS1R2sp2lo3slo4SLOS4SLOL3SLO4ALOxS2sp3sp1FS1R2sp2PP1P3END3BUF3CUR1d2bs3PP02B12B22B32B54CUR02p02FB3sp13cur3Hp13ACV3SPR2F04CPOS4SP1R3BCE2q13SLw3LR13Hq13HqLS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B32B53DPB4CUR02D12p02FB3sp13cur3Hp13ACV3SPR2F04CPOS4SP1R3BCE2q13SLw3LR13Hq13HqLS3END2q13SLw3HqLFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFS1P3END2p05nodes3CNT2q14Hq1rS1R2sp2PP1P3END3BUF3CUR1d2bs3PP02B12B22B54CUR02p02FB3sp13cur3Hp13SPR2F04CPOS4SP1R2q13SLw3LR13Hq1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFS2rv3Hrv1r2Kr1q1HS3BUF2bs3B47S1i2HiFS1R2lo3LOSS2FBS1R2sp2PP2lo4PPLO3SLO3sp13SP1S1R2sp2lo3SLO3LOS2FB3sp13SP13ALO2F1S1P3END1d2p03Hp13Hp22q14Hq1rFS1P3END1d2rv3HrvFS1P3END2p05nodes3CNT3KNBFFFS2FB2r03F641q1r1H2H02q02H43sp14SP1MFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFFFS1R2sp2PP1P3END3CUR1d2bs2FB3sp13cur2rv3HrvS3BUF2bs2FB3APBSS2sp2lo3sp13SP1S1R2sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS2p03sp13SP12rv3Hp13Hp23ALO3SPR3BCE2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP12rv3SPR3CLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP12rv3ALO3SPR2F12HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP04PPLO2B24CUR05CURLO3SLO3SPRS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP12rv3SPR3CLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO3sp13SP13SPRS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP12rv3ALO3SPR2F12HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP12rv3SPR3CLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP12rv3SPR3CLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP12rv3ALO3SPR2F12HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3sp12rv3BLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP12rv2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3ALO3SPR2F1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP1S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP12rv3SPR3CLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B24CUR05CURLO2D13SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3CUR1d2bs3LFBFS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR1d2bs3LFBFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13SP13SPRS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3F643SPR2F04CPOS4SP1RFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS3sp13SP13ALO3SPRFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13SP13SPRS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp14SP1R2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP1FFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP1S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP12rv2HB5Ha_st5Hl_stFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS2p03sp12rv3SP13Hp13Hp23ALO3SPR3BCE2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS3sp12rv3SP13ALO3SPR2HB5Ha_st5Hl_stFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOSS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS3sp12rv2HB5Ha_st5Hl_stFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33DPB4CUR05CURLO3SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33DPB4CUR05CURLO3SLO3LOS2p03sp12rv3SP13Hp13Hp23ALO3SPR3BCE2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFBFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS3ALO3SPRS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp12HB5Ha_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp12rv3SP12HB5Ha_st5Hl_stFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13SP13SPR2rv2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur2rv3SP13SPR3CLO2HB5Ha_st5Hl_stFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3ALP3PP02B22FB3sp13cur3SPR2F04SP1RS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP2p03sp12rv3Hp13Hp23SPR2HT2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP3SPR2HTFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS2p02FB3sp13cur2rv3SP13Hp13Hp23ALO3SPR2F13CLO3BCE2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13SP13SPRFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp14SP1RS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2F0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2F0". (* [comment removed for export] *)
  #[using="IMG CALLOC GETTAG FREEL LFB ALP PP0 CWP PPLO HBY BIN B1 B2 B3 B47 B5 B30 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS err_exit' l2_walk'"] Lemma outer_walk : forall p0,
    (forall p' es', p0 < p' -> InnerOb p' es') -> (forall p', p0 < p' -> OuterOb p') -> OuterOb p0.
  Proof.
    intros p0 KIN KOUT. unfold A_x509_get_name_E.OuterOb.
    intros FB sp1 w0 w1 w2 ga gb b4 j0 j96 nodes cur PHIx FFRx mc moc hc jo olen j1 vlen j2 mg' p7 xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
           D W0 W1 W2 W3 W4 PPc Hp1 Hp2 CNT PHI FFR BUD BUDF UW.
    pose proof D as D0. nvA_open D. rt_facts. walk_prep. cur_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NRT; lia).
    assert (NN : 0 <= Z.of_nat (length nodes)) by (clear; lia).
    assert (KD : Z.of_nat (length nodes) <= NB / 6) by (assert (KNB : p0 - P <= NB) by (clear - Hp2; lia); apply Z.div_le_lower_bound; [clear; lia| clear - CNT KNB; lia]).
    pose proof (blocks_below_hm R HIA hc _ _ mc _ HHc ltac:(intros b Hb; exact Hb)) as BBc.
    destruct (BBc (BUF, n) ltac:(apply SUBL; exact BIN)) as [_ BCE]. cbn [fst snd] in BCE. clear BBc.
    (* [comment removed for export] *)
    lazymatch type of HHc with HM _ _ _ _ ?LBh ?LFh _ =>
      assert (INHq : @In blk (FB, 24) (@app blk LBh (fdata LFh))) by (apply in_or_app; right; cbn; left; reflexivity);
      assert (INDq : @In blk (FB + 32, 128 - 40) (@app blk LBh (fdata LFh))) by (apply in_or_app; right; cbn; right; left; reflexivity)
    end.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HH) as ABc end end.
    frame_aobj FSH (FB + 64) 1%nat as OGB.
    pose proof GETTAG as GT'. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG_G in GT'.
    pose proof (conj PPc (conj GB (conj STlo I))) as CBOX. clear PPc GB STlo.
    acallxA_sp_keep sp1 MUk WMk
      (eapply GT' with (CS := hcs asegs R HIA hc) (PP := PP) (LENP := FB + 64) (P := p0) (END := END) (BUF := BUF) (bs := bs) (tag := 49) (lo := lo) (lenv := gb);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ gt_side CBOX OGB ABc BCE
               | lazymatch goal with
                 | |- BUF <= p0 => clear - B1 Hp1; lia
                 | |- p0 <= END => exact Hp2
                 | |- END <= BUF + _ => exact B3
                 | |- PP + 8 <= FB + 64 \/ _ => clear - APP; lia
                 | |- _ = 0 \/ FB + 64 + 8 <= BUF \/ _ => right; clear - APB; lia
                 | |- (FB + 64) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                 | |- 0 < FB + 64 => clear - F0; lia
                 | |- FB + 64 + 8 <= sp1 - 16 \/ _ => left; clear - F1 ALO LOS SLO SP1 NS1 NRT; unfold A_x509_get_name_A.STKn in SLO; lia
                 end
               | match goal with |- ?g => idtac "GT0-PRE-LEFT:" g end ]).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "GT0-LEFT:" g end.
    clear ABc OGB GT' CBOX.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rv end.
    match goal with H : _ < rv <= 0 |- _ => rename H into Hrv end.
    match goal with H : rv = 0 -> _ |- _ => rename H into HL0 end.
    match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into PPc; rename qq into q1 end.
    match goal with H : rw_cells _ _ (FB + 64) [C8 ?lw] |- _ => rename H into GB; rename lw into SLw end.
    match goal with H : p0 <= q1 <= END |- _ => rename H into Hq1r end.
    pose proof (bv_unsigned_in_range 64 SLw) as LR1. unfold bv_modulus in LR1. cbn [Z.pow Z.of_N Pos.pow] in LR1.
    gt_sync MUk WMk cur sp1 FB (FB + 64).
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr.
    { (* [comment removed for export] *)
      do 3 (step; zsimp).
      rewrite (swrap32_land_errsum rv 18446744073709542528) by (clear - Hrv; lia).
      start_Wsf cur (sp1 + 72) FB. blo sp1 SP1. zpre. wsyncsf.
      assert (RNZ : rv <> 0) by (clear - Kr Hrv; change 18446744073709551615 with (Z.ones 64) in Kr; rewrite Z.land_ones in Kr by lia; intros ->; apply Kr; reflexivity).
      go_err W0 W1 W2 W3 W4 ltac:(clear - PHI FFR CNT KD Hp1 Hp2 NN Hq1r Hrv RNZ). }
    assert (R0 : rv = 0) by (clear - Kr Hrv; change 18446744073709551615 with (Z.ones 64) in Kr; rewrite Z.land_ones in Kr by lia; Z.div_mod_to_equations; lia).
    subst rv. destruct (HL0 eq_refl) as [Hq1 HqL]. clear HL0 Kr Hrv.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    nvA_rebuild D3.
    intros moq [HKq MFq].
    eapply (inner_walk q1 (q1 + bv_unsigned SLw));
      first [ eapply nvA_mo; [exact D3| exact HKq| exact MFq] | exact W0 | exact W1 | exact W2 | exact W3 | exact W4 | exact PPc
            | exact PHI | exact FFR | exact BUD | exact BUDF | exact UW
            | lazymatch goal with
              | |- forall p' es', q1 < p' -> _ => intros p' es' Hp'; apply KIN; clear - Hp' Hq1; lia
              | |- forall p', q1 < p' -> _ => intros p' Hp'; apply KOUT; clear - Hp' Hq1; lia
              | |- P <= q1 => clear - Hp1 Hq1r; lia
              | |- q1 <= q1 + _ => clear - LR1; lia
              | |- q1 + _ <= END => clear - HqL; lia
              | |- 6 * Z.of_nat (length nodes) <= q1 - P => clear - CNT Hq1r; lia
              end
            | match goal with |- ?g => idtac "OUT-IN-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L26728691728.91 L59310676310.141L59310676311.14500001:01c035S2LF2sp2PP1P3END3BUF3CUR2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D11k1p2Hk2p'3Hp'S2LF2sp2PP3END3CUR1d2bs3LFB1p2Hk5nodes2H7S2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D11p2Hk2es5nodes2H72H8". (* [comment removed for export] *)
  #[using="IMG CALLOC GETTAG FREEL LFB ALP PP0 CWP PPLO HBY BIN B1 B2 B3 B47 B5 B30 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS err_exit' l2_walk'"] Lemma loops : forall (k : nat) (p : Z), END - p < Z.of_nat k -> (forall es, InnerOb p es) /\ OuterOb p.
  Proof.
    induction k as [|k IH]; intros p Hk.
    - split; [intros es|]; [unfold A_x509_get_name_E.InnerOb| unfold A_x509_get_name_E.OuterOb]; intros; exfalso; lia.
    - assert (KIN : forall p' es', p < p' -> InnerOb p' es') by (intros p' es' Hp'; apply (proj1 (IH p' ltac:(lia)))).
      assert (KOUT : forall p', p < p' -> OuterOb p') by (intros p' Hp'; apply (proj2 (IH p' ltac:(lia)))).
      split; [intros es; apply inner_walk; assumption| apply outer_walk; assumption].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L10818113471.8500000nS2LF2sp2PP1P3END3BUF3CUR2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D11p". (* [comment removed for export] *)
  #[using="IMG CALLOC GETTAG FREEL LFB ALP PP0 CWP PPLO HBY BIN B1 B2 B3 B47 B5 B30 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS err_exit' l2_walk'"] Lemma outer_start : forall p, OuterOb p.
  Proof. intros p. destruct (loops (Z.to_nat (END - p + 1)) p) as [_ H]; [lia| exact H]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation S1P := (A_x509_get_name_A.S1P R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP P END BUF CUR lo slo bs j48 mg pad7).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0>L12274448347.1L17455583378.1L2275137097.0 L26892418956.1L39789404379.1L40281191306.3L47209170218.1L47742554075.1L48635732457.0L56949123658.1L64630569949.300000500800900=00B00K00N00S00T00W00`S3CURS1dSS2spS3CURS1R3HIA1hS1PS3CURSS1PS1R3HIA1h". (* [comment removed for export] *)
  #[using="IMG CALLOC GETTAG FREEL LFB ALP PP0 CWP PPLO HBY BIN B1 B2 B3 B47 B5 B30 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS err_exit' l2_walk'"] Lemma from_S1P :
    havol asegs R HIA h + PHIn NB <= AVOL_MAX -> hfr asegs R HIA h + FFRn NB d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    forall ms, S1P ms -> aevtA asegs (KF asegs R HIA h mo0) POST ms.
  Proof.
    intros BUD BUDF UW ms HS1.
    ddestruct HS1 as (FB & sp1 & h1 & m1 & x1 & t0 & t1 & t2 & a0 & a1 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & w0 & w1 & w2 & ga & gb & j0 & j96
                    & Ems & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & GA & GB & FSH & SAVE & RSL & SThi & STlo & MI1
                    & PPc & HCB & BYc & OPP & OCUR & OBUF & APP0 & APC0 & APB0 & PRES0 & SS1).
    subst ms. intros moc [HK0c MF0c].
    rt_facts.
    (* [comment removed for export] *)
    unfold name_blob in HCB.
    apply (rw_cells_split_CB asegs m1 CUR [] 48 j48 [C8 (Z_to_bv 64 0); C1 mg; CB 7 pad7] [8; 8; 16; 8; 8]%nat) in HCB; [| reflexivity].
    cbn [mk_CB_cells app] in HCB.
    chunk_split HCB 1%nat W0 HN1. chunk_split HN1 1%nat W1 HN2. chunk_split HN2 1%nat W2 HN3. chunk_split HN3 1%nat W3 W4.
    replace (CUR + 8 + 8) with (CUR + 16) in W2, W3, W4 by (clear; lia).
    replace (CUR + 16 + 16) with (CUR + 32) in W3, W4 by (clear; lia).
    replace (CUR + 32 + 8) with (CUR + 40) in W4 by (clear; lia).
    cb8_to_c8 W1 (@nil cell). cb8_to_c8 W3 (@nil cell).
    assert (G1 : nvA FB sp1 w0 w1 w2 ga gb (Z_to_bv 8 248) j0 j96 (nLB []) [] CUR 0 0 m1 moc h1).
    { destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS) as (CFB & _).
      assert (HCS1 : forall x, CS x -> hcs asegs R HIA h1 x) by (intros x Hx; rewrite Ehcs; exact Hx).
      split; [exact HH1|]. split; [apply (proj2 (HKI moc)); exact HK0c|]. split; [exact MF0c|].
      split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact HCS1|].
      split; [rewrite Evol; clear; lia|]. split; [rewrite Efr; clear; lia|].
      split.
      { eapply (presW_hmono R HIA h h1 LB LF _ _ _ m m1); [| exact HCS1| exact Estk].
        ddestruct PRES0 as (P0 & C1' & C2' & C3'). split; [| split; [exact C1'| split; [exact C2'| exact C3']]].
        eapply presA_weaken; [exact P0| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact I]. }
      split; [exact SP1|]. split; [exact SP1M|]. split; [exact F64|]. split; [exact FRSH|]. split; [exact CFB|].
      split; [exact FHD|]. split; [exact GA|]. split; [exact GB|]. split; [exact FSH|]. split; [exact SAVE|]. split; [exact RSL|]. split; [exact SThi|]. split; [exact STlo|].
      split; [exact BYc|].
      split; [rewrite Ehcs; exact OPP|]. split; [rewrite Ehcs; exact OCUR|]. split; [rewrite Ehcs; exact OBUF|].
      split; [exact MI1|]. split; [exact SS1|].
      split; [intros b Hb; exact Hb|]. split; [intros x []|].
      split; [constructor|]. split; [intros x []|]. split; [left; split; reflexivity|]. split; [left; reflexivity|].
      split; [exact I|]. rewrite Ehcs. exact OCUR. }
    clear HH1 HKI FHD GA GB FSH SAVE RSL SThi STlo MI1 BYc OPP OCUR OBUF PRES0 SS1 SP1 SP1M F64 FRSH Ehtop Estk Eflag Evol Efr APP0 APC0 APB0.
    eapply (outer_start P FB sp1 w0 w1 w2 ga gb (Z_to_bv 8 248) j0 j96 [] CUR 0 0 m1 moc h1);
      first [ exact G1 | exact W0 | exact W1 | exact W2 | exact W3 | exact W4 | exact PPc | exact BUD | exact BUDF | exact UW | exact B2
            | lazymatch goal with
              | |- P <= P => clear; lia
              | |- 6 * Z.of_nat (length _) <= P - P => cbn [length]; clear; lia
              | |- 0 <= _ => cbn [length]; clear; lia
              end
            | match goal with |- ?g => idtac "S1P-OUT-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.

  #[using="IMG UARG SM1 CALLOC GETTAG FREEL"] Theorem A_x509_get_name_specE : x509_get_name_stmtE asegs R HIA PHIn FFRn CNTn STKn A_X509_GET_NAME.
  Proof.
    intros h LB LF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo PP CUR P END BUF lo slo d bs j48 mg pad7.
    unfold NAME_SIZE.
    intros HH HK0 LFB HPP ALP PP0 OPP CWP PPLO HBY BIN B1 B2 B3 B47 B5 B30 DPB HCUR ALC CUR0 OCUR CWC CURLO DCB D1 ST SS SLOS SLOL SLO TOP SPA SPH MI TPV NDL BUD UW BUDF -> -> ->.
    pose proof (hm_aobj_block asegs R HIA h _ _ m BUF (Z.of_nat (length bs)) HH BIN) as OBUF.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ _ (conj HK0 (mo_frame_refl mo))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo).
    { eapply (A_x509_get_name_A.pro_walk R HIA) with (lo := lo) (slo := slo) (bs := bs) (P := P) (END := END) (j48 := j48) (mg := mg) (pad7 := pad7);
        first [ exact HH | exact HPP | exact HBY | exact HCUR | exact CWP | exact CWC | exact ST | exact SS | exact OPP | exact OCUR | exact OBUF | exact SLO | exact MI
              | eassumption | match goal with |- ?g => idtac "PW-LEFT:" g end ]. }
    intros ms1 HS1.
    eapply from_S1P with (bs := bs);
      first [ exact HPP | exact HBY | exact HCUR | exact CWP | exact CWC | exact SLO | exact BUD | exact UW | exact BUDF | exact HS1
            | eassumption | match goal with |- ?g => idtac "TH-LEFT:" g end ].
  Qed.

  (* [comment removed for export] *)
  #[using="IMG UARG SM1 CALLOC GETTAG FREEL"] Theorem A_x509_get_name_spec : x509_get_name_stmtA asegs R HIA PHIn FFRn CNTn STKn A_X509_GET_NAME.
  Proof. exact (x509_get_name_stmtE_A asegs R HIA PHIn FFRn CNTn STKn A_X509_GET_NAME A_x509_get_name_specE). Qed.
End Walk.
