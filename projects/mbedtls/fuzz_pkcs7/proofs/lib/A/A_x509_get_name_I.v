(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_x509_get_name_A.     (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_len
     A_asn1_free_named_data_list_shallow A_crt_stmts A_crt_parse_stmts A_pkcs7_getcerts A_mpi_stmtA A_x509_get_name_stmt A_x509_get_name_stmtE A_x509_get_name_A A_x509_get_name_B A_x509_get_name_C A_x509_get_name_D A_x509_get_name_E A_x509_get_name_F A_x509_get_name_G A_x509_get_name_H.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "07n0@D10636937134.266D10636937134.296D10780387598.266D10916531869.278D16071854214.266D16071854214.296D16901939902.266D16901939902.296D2457516971.266 D25887797116.278D32458870384.266D46794843979.266D46794843979.296D60109196847.278D60109446735.266D60109446735.296D65752989693.296D8009443288.296 K11185843281.296K14662993782.278K1932217360.266 K1932217360.296 K19511088946.296K20592461617.266K20981739667.266K20981739667.296K23672143632.266K23672143632.296K29378133114.266K30993319891.266K30993319891.296K34516387472.266K35028229553.266K36444357201.296K40598034112.266K40598034112.296K44164039966.278K45872506161.266K48593550302.278K49541715106.266K52599012741.278K56730913969.266K57332385994.296K59713869701.278K59810587792.266K59810587792.296K65858155712.296K67298046963.266K67298046963.296L10660966017.8  L11179310391.2  L11301983443.2  L11431517604.16 L11949961375.1  L12140462837.3  L13199424673.6  L14647789168.2  L15471821837.260L15479883060.4  L15934535645.1  L16641873078.1  L16772002776.267L16772002776.268L1685717371.0   L17523603370.267L17523603370.268L17723511885.5  L1848725797.263 L1848725797.265 L18529518550.274L18549529655.5  L1942461814.2   L19497174612.2  L19914454641.3  L20115763962.9  L20594349655.2  L20923585658.2  L20977711877.2  L22923672419.263L22925878376.266L23136739156.1  L23657246326.2  L2385600136.1   L24023900370.0  L2487024120.2   L2487147605.2   L2621559066.1   L26368079009.0  L26443884051.264L26443884051.266L27111942217.1  L27163688480.4  L27826531539.1  L27832436220.243L27940405558.8  L28046422800.4  L28316294259.15 L29311549712.258L29311754221.260L29391009772.3  L30507144274.2  L3055355236.3   L30997223346.3  L31393302313.265L31393302313.267L31789301242.2  L33851503706.2  L34522961910.2  L35017493719.2  L35139482716.0  L35497690860.3  L35497693828.3  L35627047303.1  L35666023782.10 L36451390263.2  L37156630869.0  L38235734261.1  L38383890888.1  L38692377683.1  L39231752993.0  L39332637397.0  L40228640085.0  L40585223510.2  L40714693207.6  L41202929119.259L41251426164.1  L41601820452.5  L42248755539.1  L42411609006.0  L42488948659.2  L42894740255.1  L43230691980.3  L43301826312.1  L43317676572.3  L43595757740.2  L44166661144.3  L44465449044.261L44467548957.258L45653528320.3  L45883208791.2  L46512611463.267L47870616696.2  L47899738467.2  L48117785831.9  L48455046775.1  L48596171480.2  L49233373885.2  L49478371288.2  L4951167123.267 L49526752708.2  L50925318027.2  L52610022531.2  L53115519699.1  L53404531630.9  L53505134330.2  L56459574803.20 L56461361441.10 L56464645271.1  L56499015653.262L56500720864.260L56694929206.266L56694929206.268L56732278231.2  L57130527895.2  L57338894764.3  L57387013391.2  L576250137.257  L58039649675.2  L58451383419.10 L58972524609.3  L59308579414.10 L59308586248.2  L59723830915.2  L59795174902.2  L60098763854.6  L60812373952.10 L61655438821.18 L61655438821.20 L61672228356.262L62586168108.2  L63915962791.1  L64009471222.1  L64148832490.243L64370849402.2  L65762635419.1  L65862516566.2  L66151427842.16 L66298372189.2  L66812728480.3  L67070089790.2  L67304579733.2  L67473393319.1  L8171953640.243 L881835912.0    L9080220944.4   L9356559676.15  L9619762727.1   L9748633241.2   O10644243082.266O10644243082.296O10871149737.266O10871149737.296O1254725598.266 O14075571866.266O14075571866.296O14632083704.266O14912726833.266O14912726833.296O16958666856.296O17217116232.266O17217116232.296O18101220210.296O18988691132.266O18988691132.296O20866770946.266O21298244344.266O21298244344.296O22525005962.296O24222861850.266O24222861850.296O2450246008.266 O2450246008.296 O28973706943.296O30010457231.266O33449646875.266O33449646875.296O33496826488.266O33496826488.296O3493317847.266 O3493317847.296 O37559489567.266O37559489567.296O3821773283.266 O3821773283.296 O44938202843.266O44938202843.296O45637135587.296O4776649498.266 O4776649498.296 O49701823576.266O50809583907.266O52301174499.296O54119978487.266O54119978487.296O56327351971.266O57031441090.266O58364443802.266O63008166051.266O63748625294.296O64474006218.266O64474006218.296O6468225490.296 O6468421667.266 O65961212488.296P11295933877.296P19899262166.266P20934313244.266P30511339222.266P30511339222.296P3069564867.266 P3069564867.296 P31778598044.266P31778598044.296P38605639612.249P38605639612.273P38605639612.274P42484919333.266P43594459594.296P45663739494.296P47876372191.266P47876372191.296P49230739482.266P50927926572.296P51370907562.249P51370907562.273P51370907562.274P53346601986.249P53346601986.273P53346601986.274P53515870108.266P53515870108.296P57140489617.278P58041177900.266P58041177900.296P62587740714.278P64359622428.266P64359622428.296P66292560634.266P66292560634.296P66818508295.266P66818508295.296P66903681610.249P66903681610.273P66903681610.274P67064334489.266P67064334489.296P7740881908.249 P7740881908.273 P7740881908.274 P9764112383.266 P9764112383.296 Q10592533181.266Q10636937134.266Q10636937134.296Q10646134994.266Q10646134994.296Q10649498890.265Q10651751606.264Q10663072064.266Q10665153022.269Q10665153022.273Q10821824020.249Q10821824020.273Q10821824020.274Q10914612381.277Q10916531869.278Q11133374175.266Q11657053839.266Q11938624351.296Q12465444467.233Q12658605510.249Q12658605510.251Q12658605510.273Q12658605510.274Q12658605510.275Q12658605510.276Q12773147547.274Q13733105547.264Q13846928860.266Q13846928860.296Q13851160440.265Q14394173634.269Q14394173634.273Q1553561799.269 Q1553561799.273 Q15930096381.269Q15979578007.269Q15979578007.273Q16429527224.266Q16429527224.296Q16626982297.273Q16796962909.239Q17027695041.266Q17027695041.296Q17681074618.266Q17681074618.296Q17701933584.265Q17841111261.246Q18087146764.267Q18087146764.268Q18897435335.269Q18897435335.273Q19561597574.243Q19868621735.296Q19953245935.266Q19953245935.296Q21767670690.266Q21767670690.296Q23481527360.269Q23702429453.266Q25887797116.278Q26295627581.274Q27573751300.266Q27573751300.296Q27942454161.266Q27942454161.296Q2803826605.266 Q2803826605.296 Q28420499829.271Q28552026580.269Q28552026580.273Q29775981542.266Q29775981542.296Q30222614424.266Q3054610265.239 Q30926961810.269Q30926961810.273Q31526414380.249Q31526414380.273Q31526414380.274Q31997470964.267Q3215835802.244 Q32458870384.266Q32681607669.266Q32681607669.296Q33137450695.266Q33137450695.296Q33283861378.249Q33283861378.273Q33283861378.274Q33306674327.269Q33306674327.273Q34292258162.269Q34292258162.273Q34357517856.243Q34390149656.265Q34669208222.244Q34964695579.242Q35662748640.238Q38080925904.296Q38105515555.269Q38372880008.241Q38383642699.271Q38385314999.274Q38385659317.274Q39600066516.265Q40354196046.249Q40354196046.273Q40354196046.274Q40360481330.234Q41086062499.269Q41086062499.273Q41675861917.237Q42439168719.266Q42439168719.296Q42439443119.278Q42441548847.249Q42441548847.273Q42441548847.274Q42887926878.240Q43138029699.249Q43138029699.273Q43138029699.274Q43438798406.274Q43479930840.266Q43479930840.296Q43610412201.266Q43622973458.276Q44298944140.234Q44301027056.249Q44301027056.273Q44301027056.274Q45317270253.266Q45482765142.251Q45482765142.275Q45482765142.276Q46794843979.266Q46794843979.296Q47799716979.233Q47799716979.267Q47799716979.268Q48118064779.266Q48119910507.249Q48119910507.273Q48119910507.274Q48211510750.266Q50160428632.296Q52314950583.269Q52314950583.273Q52445207949.267Q53315247896.266Q53667029527.269Q53667029527.273Q54481541668.243Q5596578838.249 Q5596578838.273 Q5596578838.274 Q56204695986.266Q56204695986.296Q56530976407.266Q58763128337.269Q59023939651.275Q59615732211.267Q59615732211.268Q59865321072.278Q59865603600.266Q59865603600.296Q59867425008.249Q59867425008.273Q59867425008.274Q60578270726.274Q60952393704.269Q60952393704.273Q61847600945.265Q62190329447.266Q63733638937.237Q64228675114.248Q64228675114.272Q64228675114.273Q64650680438.241Q64681563910.249Q64681563910.273Q64681563910.274Q64683667846.278Q64683942374.266Q64683942374.296Q65752674778.240Q65752989693.296Q68043645948.277Q68077445246.267Q68077445246.268Q68519243108.238Q6863764061.242 Q6912043747.246 Q7174379670.274 Q7657711383.269 Q7657711383.273 Q8009443288.296 Q8945570139.271 Q9350530486.243 Q9350530486.273 Q9485152634.249 Q9485152634.273 Q9485152634.274 Q9487243258.278 Q9633850233.243 Q9644583048.266 Q9644583048.296 Q97189773.269   Q97189773.273   00000Z01D01n02j04U06a08=09Y09Z0:V0;@0;j0<T0=W0>H0?90?c0@M0A_0B\0Ck0E90FK0G[0Hf0J70KF0LT0Mc0NJ0O10P@0QP0Rb0Sm0U>0V;0WK0XD0YT0ZQ0[a0]30^00_?0`M0a^0bm0d;0dW0dX0dY0eA0eF0eR0eg0eh0gj0h90h<0hA0hB0hC0hD0iO0jZ0jm0kW0lA0m20mC0mD0mE0mF0mg0mh0mi0mj0o@10V10[10\10a10b10c10d10i10j11T12>12B12R12W13A13V13e14H14I14J14K14L14M14N15815b15c15m15n15o16016116216916O16P16Q16U16Z16_16`16a16b16c17917c17g18918>18?18@18E18Q18U18`18a18b1:_1<\1<]1<^1=H1=I1=Q1>11>51>61>71>?1>i1>j1>k1>l1?11?R1?S1?c1@@1@A1B71Cm1DW1EA1EB1EC1ED1EK1F51F61FG1FS1Fd1Fj1Fk1Fl1G61GS1H61HY1HZ1H[1H`1Ha1Ik1Il1J11J21J]1J^1J_1J`1Ja1Jf1Jg1Jh1K71K\1Ka1Kb1Kc1Kd1Ke1Kf1Kg1Kh1Ki1Kj1Kk1Kl1Km1Kn1Ko1L01L11L21L31L41L51L61L71L81L91L:1L;1L<1L=1L>1L?1L@1LA1LB1LC1LD1LE1LF1LG1LH1LI1LJ1LK1LL1LM1LN1LO1LP1LQ1LR1LS1LT1LU1LV1LW1LX1LY1LZ1MX1Nd1P?1QZ1S[1U>1WG1Xb1Z^1[]1\\1][1^_1_e1`k1b71cC1dO1e[1f[1g[1h[1j21l?1mV1o120m22=23^25`27828S2:O2;62;]2=92>U2?P2@K2AF2Bi2E22Em2Fh2Gc2I>2K:2K\2L;2LZ2L[2L\2M;2MZ2O82PV2R42Ro2Sj2Te2UZ2VO2W12W22WU2X72Y22ZC2[>2\92]J2^[2_>2_]2_^2__2_`2_a2_b2_c2_d2`C2`D2`E2aK2bQ2d;2e02eO2en2gQ2iZ2j92jj2kL2kn2ko2l02mJ2mm2mn2mo2oJ31F31h31i32^33=33>33?34R36F36i37L37o38038138X39?39a3:V3:W3:X3:Y3:Z3:[3;>3;o3<Q3<R3<S3==3=g3=h3=i3=j3=k3=l3=m3=n3>b3>c3?T3A93An3BQ3C_3DT3E73EZ3F=3F>3G53Gl3Hc3IH3II3IJ3J?3Jg3KO3LM3MM3NM3OM3PB3PC3PD3PE3Ph3RK3TT3U33U_3VD3W;3X23Xi3Xj3Z;3[L3\]3]<3][3^=3^_3_A3`?3aU3ca3e73fa3fb3fc3fd3gG3gH3gI3gJ3hR3hS3hT3hU3hV3hW3hX3jB3jm3jn3jo3k03k13k23k33k43k53kX3kY3kZ3l[3m=3n23oa42743l44a46N48e4:h4=44>I4@?4A44AW4BL4Bn4CP4DE4EA4F24FZ4F[4F\4G?4G^4HF4Hn4Ii4Jd4K_4LW4M<4Ma4NF4NG4NHS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS2FB3sp13cur3SP13SPR2F04CPOS4SP1RS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS2p02es2FB3sp13cur3SP13Hp13Hp33SPR2F04CPOS4SP1R2q13L1w3Hq13HqL3KL0S1R3HIA1h2LF2sp2PP1P3END3CUR1d2bs3LFB3PP02B24CUR03TOP2FB3sp13cur2hc3HTc3SP13SPR2F04CPOS4SP1RS1R3HIA1h2LF2sp2PP1P3END3CUR1d2bs3LFB3PP02B24CUR03TOP2FB3sp13cur2hc3HTc3SP13SPR2F04CPOS4SP1RFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13cur2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13curS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur3x294CFBa2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2ob4CFBa2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur3x293CPP2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur3x294CFBa2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x144CFBa2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13x143APP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur3x293APP2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur3x293CPP2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB2p02es2FB3sp13x143APB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3DPBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3DPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x144CFBa2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur3x294CFBa2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13x143APP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur3x293APP2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3cur3CBF2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x144CFBa2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2ob3CPP2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x144CFBa2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2ob4CFBa2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x144CFBa2x23x153x163x174POSTS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3sp13cur3x293CBF2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2ob4CFBa2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur3x293CPP2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13cur3x293APP2q13L1w3x173x303x313x324POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02es2FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13cur3x293CPP2q13L1w3x173x303x313x324POSTS1P3BUF2B12p02es3Hp12q14Hq1rFFS1R2sp3BUF2lo2bs3SLO3LOS3sp13SP13ALO3BCES3CURS2q13L1w3LR1S1P3END2p02es3Hp23Hp3FS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12p02es2FB3sp13cur3Hp13Hp33SPR2F04CPOS4SP1R2q13L1w4Hq1r3Hq13HqL3KL0S3BUF2bs2FB3APBS1lS3curFFSS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2HB5Ha_st5Hl_st5SAEst5CM8st2x22HxS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2HB5Ha_st5Hl_st5SAEst5CM8st2x22HxS2p02q13L1w3Hq13KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3sp13cur2q1S1P3BUF2B12p03Hp1FFFS1P2p02es3Hp12q13L1w4Hq1r2q24Hq2rFFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3SPH2FB3sp13cur3SPR2F04CPOS3CLO4SP1RS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3SPH2FB3sp13cur3SPR2F04CPOS3CLO4SP1RS3curFS3curSFSS3sp1SS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS2PPS3BUF2bs3cur3CBFS3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2sp2lo3SLO3sp13SP1S2es2q13L1w3HqLS1R2sp2lo3SLO3LOS2FB3sp13SP13ALO2F1FFFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFS3cur4CPOSFFSSSS5nodesS1R3HIA1h2sp2lo3TOP2HTFSS2loS3curS3curSSSFS3END3BUF2bs2B32es3Hp3S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS2FBS2p02q13Hq12q23HqOS3curSFS3curS2PP3cur3CPPS2FBS2PP2FB3APPFFS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B32B53DPB4CUR02D12p02es2FB3sp13cur3Hp13Hp33ACV3SPR2F04CPOS4SP1R3BCE2q14Hq1r3Hq1S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B32B53DPB4CUR02D12p02es2FB3sp13cur3Hp13Hp33ACV3SPR2F04CPOS4SP1R3BCE2q14Hq1r3Hq1FFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFS2rv3HrvS1R2sp2lo3slo4SLOS4SLOL3SLO4ALOxS2FBFFS2sp3sp1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFFFS3curS3END3BUF2bs2B32es3Hp32q13L1w3HqLFS1P3END1d2rv3HrvS1R2sp2lo3SLO3sp13cur3SP13CLOFS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12p02es2FB3sp13cur3Hp13Hp33SPR2F04CPOS4SP1R2q14Hq1r3Hq1S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12p02es2FB3sp13cur3Hp13Hp33SPR2F04CPOS4SP1R2q14Hq1r3Hq1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFFFS2FB2F0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFS2rv3Hrv1r2Kr1q1HS3BUF2bs3B47S2rv3Hrv1r2KZ1q1HS1i2HiFFS1R2lo3LOSS1R2sp2PP2lo4PPLO3SLO3sp13SP1S1P3END1d2p02es3Hp13Hp23Hp32q14Hq1rS1P3END1d2p02es3Hp13Hp23Hp32q14Hq1rFFS3curFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13cur2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxFS3curFS2FB2r03F641q1r1H2H02q02H43sp14SP1M3cur3CALFFFFS3curFSS2sp2lo3sp13SP1S1R2sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS3curFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3cur3SPR3CLOS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3ALO3SPR3BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS2p02es3Hp13Hp33ALO3SPR3BCE2q13L1w4Hq1r3Hq13HqL3KL0S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS2p02es3sp13SP13Hp13Hp33ALO3SPR3BCE2q13L1w4Hq1r3Hq13HqL3KL0S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2p02es3sp13cur3SP13Hp13Hp33SPR3CLO2q13L1w3Hq13HqL3KL0S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3APB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3APB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB3APB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3ALO3SPR2F1S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4CFBa2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4CFBa2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur4CFBa2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB3PP02B24CUR04SLOS2FB3ALO3SPR2F12HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D14SLOS2p02es2FB3Hp13Hp33ALO3SPR2F12q13L1w3Hq13HqL2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB3PP02B24CUR04SLOS2FB3ALO3SPR2F12HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2p02es3sp13cur3SP13Hp13Hp33SPR3CLO2q13L1w3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3cur2ob3SPR3CLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS2p02es2FB3sp13SP13Hp13Hp33ALO3SPR2F12q13L1w3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP12ob3SPR3CLO2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2p02es3sp13cur3SP13Hp13Hp33SPR3CLO2q13L1w3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP1S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B24CUR05CURLO2D13SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B24CUR05CURLO2D13SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APC2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APC2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APC2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS2p02es3sp13SP13Hp13Hp33ALO3SPR3BCE2q13L1w4Hq1r3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APP2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APP2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3APP2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2p02es3sp13cur3SP13Hp13Hp33SPR3CLO2q13L1w3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR1d2bs3LFBFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12p02es3Hp13Hp33SPR2q14Hq1r3Hq1S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12p02es3Hp13Hp33SPR2q14Hq1r3Hq1S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12p02es3Hp13Hp33SPR2q14Hq1r3Hq1S1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3BCE2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3BCE2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3BCE2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFBFFFFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFBFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12p02es3Hp13Hp33SPR2q13L1w4Hq1r3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS2p02es3sp13SP13Hp13Hp33ALO3SPR3BCE2q13L1w4Hq1r3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBFFS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3F643SPR2F04CPOS4SP1RS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curFFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS3sp13SP13ALO3SPRS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS2p02es3sp13SP13Hp13Hp33ALO3SPR2q13L1w3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2q1FS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFBFFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13SP13SPRS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2p02es3sp13SP13Hp13Hp33SPR2q13L1w3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stFFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP1S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP1FFFFFFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB2HB5Ha_st5Hl_stFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO2FB3sp13SP13SPR2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B53DPB4CUR02D12p03Hp13SPR2q13Hq1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HBFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOSS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOSS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS3cur2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOS2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33DPB4CUR05CURLO3SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33DPB4CUR05CURLO3SLO3LOS2p02es3sp13SP13Hp13Hp33ALO3SPR3BCE2q13L1w4Hq1r3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2HB5Ha_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstFS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3BCE2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3BCE2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d3LFB1l2B33B473B303DPB3DCB2FB3BCE2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS3ALO3SPRS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3ALO3SPR2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13SLO3LOS2p02es2FB3Hp13Hp33ALO3SPR2q13L1w3Hq13HqL2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3ALO3SPR2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12p02es3Hp13Hp33SPR2q13L1w4Hq1r3Hq13HqL3KL0FFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp1FFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO2FB3SPR2HB5Ha_st5Hl_stFFFFFFS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12p02es3Hp13Hp33SPR2q13L1w4Hq1r3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4CPOS2HBFFFFFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3ALP3PP02B22FB3sp13cur3SPR2F04SP1RS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3F643SPR2F04CPOS4SP1R2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D12p02es2FB3sp13cur3F643Hp13Hp33SPR2F04CPOS4SP1R2q13L1w3Hq13HqL2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13cur3F643SPR2F04CPOS4SP1R2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP2FB3SPR2HT2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33B303DPB4CUR03DCB2D13TOP2p02es2FB3Hp13Hp33SPR2HT2q13L1w4Hq1r3LR13Hq13HqL2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP2p02es2FB3Hp13Hp33SPR2HT2q14Hq1r2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP2p02es3cur2ob3Hp13Hp33SPR2HT2q13L1w3Hq13HqL3KL02HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP3SPR2HTS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP2p02es3Hp13Hp33SPR2HT2q13L1w3Hq13HqL3KL0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2FB3sp13SP12HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3cur4CPOSFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3curS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp14SP1RS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp14SP1RS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3cur2ob2HB5Ha_st5Hl_stS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2F0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2F0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2F0FF". (* [comment removed for export] *)
  #[using="IMG CALLOC GETTAG FREEL LFB ALP PP0 CWP PPLO HBY BIN B1 B2 B3 B47 B5 B30 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS err_exit' l2_walk'"] Lemma inner_walk : forall p0 es,
    (forall p' es', p0 < p' -> InnerOb p' es') -> (forall p', p0 < p' -> OuterOb p') -> InnerOb p0 es.
  Proof.
    intros p0 es KIN KOUT. unfold A_x509_get_name_E.InnerOb.
    intros FB sp1 w0 w1 w2 ga gb b4 j0 j96 nodes cur PHIx FFRx mc moc hc jo olen j1 vlen j2 mg' p7 xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s10v
           D W0 W1 W2 W3 W4 PPc Hp1 Hp2 Hp3 CNT PHI FFR BUD BUDF UW.
    pose proof D as D0. nvA_open D. rt_facts. walk_prep. cur_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NRT; lia).
    assert (NN : 0 <= Z.of_nat (length nodes)) by (clear; lia).
    assert (KD : Z.of_nat (length nodes) <= NB / 6) by (apply (A_x509_get_name_A.cnt6_div _ (p0 - P)); [exact CNT| clear - Hp2 Hp3; lia]).
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
    zstep. zstep. zstep. zstep. zstep.
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
    { (* [comment removed for export] *)
      start_Wf cur FB.
      zstep.
      rewrite (swrap32_land_errsum rv 18446744073709542528) by (clear - Hrv; lia).
      zstep.
      zstep. if_cases KZ; zify_cond KZ.
      - wsyncf. go_err W0 W1 W2 W3 W4 ltac:(clear - PHI FFR CNT KD Hp1 Hp2 Hp3 NN Hq1r Hrv).
      - exfalso. clear - KZ Hrv. change 18446744073709551615 with (Z.ones 64) in KZ. rewrite Z.land_ones in KZ by lia. Z.div_mod_to_equations. lia. }
    assert (R0 : rv = 0) by (clear - Kr Hrv; change 18446744073709551615 with (Z.ones 64) in Kr; rewrite Z.land_ones in Kr by lia; Z.div_mod_to_equations; lia).
    subst rv. destruct (HL0 eq_refl) as [Hq1 HqL]. clear HL0 Kr Hrv.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. if_cases KL; zify_cond KL.
    { (* [comment removed for export] *)
      start_Wf cur FB.
      zstep. zstep. zstep.
      wsyncf. go_err W0 W1 W2 W3 W4 ltac:(clear - PHI FFR CNT KD Hp1 Hp2 Hp3 NN Hq1r). }
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    shadow_chk OBUF q1 1.
    (* [comment removed for export] *)
    get_byte bs (q1 - BUF) ob NBo. read_at BYc NBo (q1 - BUF) RDo.
    zstep. zstep.
    shadow_chk OCc cur 4.
    try clear RDo.
    (* [comment removed for export] *)
    start_Wf cur FB.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0320@D10636937134.252D16071854214.252D16901939902.252D46113380110.252D46794843979.252D56536395888.252D5984197035.252 D60109446735.252K10558392113.252K1932217360.252 K20981739667.252K23672143632.252K2870125178.252 K30993319891.252K3270517425.252 K32782467746.252K34516387472.252K35852068145.252K59810587792.252K65858155712.252K67298046963.252K68434149297.252L10564965975.2  L11431517604.16 L11949961375.1  L1212436508.3   L12730738952.1  L12811117941.3  L12950669463.6  L13199424678.4  L16641873078.1  L18023395959.1  L1848725797.249 L18549529655.5  L1942461814.2   L20923585658.2  L20977711877.2  L21065699441.3  L23657246326.2  L2487147605.2   L2621559066.1   L26443884051.250L27111942217.1  L27940405558.8  L2883004908.3   L29311549712.243L30507144274.2  L3055355236.3   L30997223346.3  L31393302313.251L31789301242.2  L3256677335.2   L32766956484.2  L33312313103.2  L34522961910.2  L34680000318.5  L35497690860.3  L35627047303.1  L35666023782.10 L35838227543.2  L37156630869.0  L38235734261.1  L38383890888.1  L39332637397.0  L40228640085.0  L41202929119.242L41663468825.242L47870616696.2  L47899738467.2  L48117785831.9  L49478371288.2  L50925318027.2  L52293817109.4  L53505134330.2  L53527181501.2  L54379384959.7  L56464645271.1  L56466211067.19 L56694502969.252L58451383419.10 L58972524609.3  L59308586248.2  L59795174902.2  L60098763854.6  L60448817524.1  L60812373952.10 L61004000883.15 L61640928013.19 L62520191992.2  L64370849402.2  L64526681523.2  L64951446305.0  L65862516566.2  L66151427842.16 L66298372189.2  L66812728480.3  L66925259772.229L67070089790.2  L67304579733.2  L68418727639.2  L8365027124.4   L881835912.0    L9080220944.4   L9356559676.15  L9748633241.2   O10871149737.252O14075571866.252O14632083704.252O14912726833.252O18664807618.252O18988691132.252O20098837283.252O21298244344.252O22525005962.252O24222861850.252O2450246008.252 O3078286936.252 O32263864995.252O33083286018.252O33449646875.252O33496826488.252O3493317847.252 O37559489567.252O3821773283.252 O38925841571.252O44938202843.252O4776649498.252 O54119978487.252O57791108643.252O58364443802.252O64474006218.252O65961212488.252O67171060367.252O8121201118.252 P20934313244.252P21063123670.252P30511339222.252P3069564867.252 P31778598044.252P47876372191.252P50927926572.252P53515870108.252P53529750042.252P64359622428.252P64538971685.252P66292560634.252P66818508295.252P67064334489.252P9764112383.252 Q10636937134.252Q10646134994.252Q10649498890.250Q10651751606.249Q1358106889.249 Q13733105547.249Q13846928860.252Q13851160440.250Q16429527224.252Q17027695041.252Q17681074618.252Q17701933584.250Q19561597574.229Q21254955245.252Q21767670690.252Q27573751300.252Q27942454161.252Q2803826605.252 Q29775981542.252Q32437204119.252Q32681607669.252Q33137450695.252Q34390149656.250Q34669522109.252Q34671230885.249Q34671339340.229Q35333735439.229Q39031261844.249Q39600066516.250Q41414298335.252Q42439168719.252Q43479930840.252Q46794843979.252Q47780987149.252Q48118064779.252Q51218566552.252Q55202259380.249Q56204695986.252Q59865603600.252Q61847600945.250Q64683942374.252Q8126701711.252 Q9350530486.229 Q9633850233.229 Q9644583048.252 00000Z02E03a04K05505_05`06Q07^08j0:20;>0<J0=10>>0?K0@W0Ad0C00D80ED0FQ0FR0G:0G?0GJ0GN0GZ0H00H>0HC0HG0I10IB0IC0ID0IE0IF0IG0IH0IM0J70J;0JP0JQ0JR0JS0JT0JU0K?0K@0KA0KB0KI0KJ0K\0K]0Kd0L:0L;0L<0L@0LE0LF0LG0M10M[0M\0Md0ND0NL0NM0N]0N^0N_0O;0O<0OL0P60PG0PS0PY0PZ0Pd0Ph0QE0Qh0RD0RE0RF0RG0RH0RI0Rl0Rm0Rn0SX0SY0SZ0S[0Sj0Sk0T:0T_0T`0Ta0Tb0Tc0Td0Te0Tf0Tg0Th0Ti0Tj0Tk0Tl0Tm0Tn0To0U00U10U20U30U40U50U60U70U80U90U:0U;0U<0U=0VX0Wd0Xe0Z80[S0\_0]k0_F0`R0am0c10cX0e40fW0h20hQ0hR0i10iP0jN0jm0jn0jo0l50lT0n70nV10010111L11M12`13C13j13k13l14V14W15915[16=16_17I17J17l18T1:71:V1:W1;U1<71<Y1<Z1<[1=\1?11?21?Z1@?1@dS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS2FB3sp13cur3SP13SPR2F04CPOS4SP1RS1R3HIA1h2LF2sp2PP1P3END3CUR1d2bs3LFB3PP02B24CUR03TOP2FB3sp13cur2hc3HTc3SP13SPR2F04CPOS4SP1RS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3LOS2FB3sp13curS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x144CFBa2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13x143APP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB2p02FB3sp13x143APB2x23x153x163x174POSTS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3DPBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x144CFBa2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x144CFBa2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x144CFBa2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13x143APP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x143CPP2x23x153x163x174POSTS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB2p02FB3sp13cur3x144CFBa2x23x153x163x174POSTFS1R2sp3BUF2lo2bs3SLO3LOS3sp13SP13ALO3BCES3CURS2PP2FB3APPS2FBS2q13SLw3LR1S1P3END2p03Hp12q14Hq1rS1P3END2p03Hp2S3curS2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1P3BUF2B12p03Hp1FFFFFSS3sp1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS2PPS1R2sp2lo3SLO3sp13SP1FFFFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFFFS2FB2F0FS2p02q13Hq12p'3Hp'SS5nodesS1R3HIA1h2sp2lo3TOP2HTFSS2loS3curSSS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFS2rv3HrvS1R2sp2lo3slo4SLOS4SLOL3SLO4ALOxS2sp3sp1FS3END2q13SLw3HqLFFS1P3END2p05nodes3CNT2q14Hq1rFS1P3END1d2rv3HrvS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curS2rv3Hrv1r2Kr1q1HS3BUF2bs3B47S1i2HiFS1R2lo3LOSS2FBS1R2sp2PP2lo4PPLO3SLO3sp13SP1S1R2sp2lo3SLO3LOS2FB3sp13SP13ALO2F1S1P3END1d2p03Hp13Hp22q14Hq1rFFFSFS2FB2r03F641q1r1H2H02q02H43sp14SP1MFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB3sp13curFFFS3BUF2bs2FB3APBSS2sp2lo3sp13SP1S1R2sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP04PPLO2B24CUR05CURLO3SLO3SPRS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3SLO3sp13SP13SPRS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3sp13SP13ALO3SPR2F1S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS2FB3ALO3SPR2F1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP1S1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B24CUR05CURLO2D13SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3CUR1d2bs3LFBFS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13SP13SPRS1R2LF2sp2PP1P3END3CUR1d2bs3LFBFFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3sp13cur3SP13SPR3CLOS1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B34CUR05CURLO3DCB3SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3CUR1d2bs3LFBS1R2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B23DPB4CUR03DCB2D12FB3sp13cur3F643SPR2F04CPOS4SP1RFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3LOS3sp13SP13ALO3SPRFS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3sp13SP13SPRS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp1S1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp13SP1FFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP1FS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3sp13SP1FS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR3slo1d2bs3LFB4SLOSS1R2LF2sp2PP1P3END3BUF3CUR2lo1d2bs3LFB3PP04PPLO2B12B22B33DPB4CUR05CURLO3SLO3LOS3sp13SP13ALO3SPR3BCES1R2LF2sp2PP1P3END3CUR1d2bs3LFBFS1R2LF2sp2PP1P3END3CUR2lo1d2bs3LFB3PP02B24CUR03SLO3LOS3ALO3SPRS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FBFFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3ALP3PP02B22FB3sp13cur3SPR2F04SP1RS1R3HIA1h2LF2sp2PP1P3END3BUF3CUR3slo1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13TOP3SPR2HTFS1R2LF2sp2PP1P3END3CUR1d2bs3LFB3sp14SP1RS1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2F0S1R2LF2sp2PP1P3END3CUR1d2bs3LFB2FB2F0". (* [comment removed for export] *)
  #[using="IMG CALLOC GETTAG FREEL LFB ALP PP0 CWP PPLO HBY BIN B1 B2 B3 B47 B5 B30 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS err_exit' l2_walk'"] Lemma outer_walk : forall p0,
    (forall p' es', p0 < p' -> InnerOb p' es') -> (forall p', p0 < p' -> OuterOb p') -> OuterOb p0.
  Proof.
    intros p0 KIN KOUT. unfold A_x509_get_name_E.OuterOb.
    intros FB sp1 w0 w1 w2 ga gb b4 j0 j96 nodes cur PHIx FFRx mc moc hc jo olen j1 vlen j2 mg' p7 xra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 s10v
           D W0 W1 W2 W3 W4 PPc Hp1 Hp2 CNT PHI FFR BUD BUDF UW.
    pose proof D as D0. nvA_open D. rt_facts. walk_prep. cur_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NRT; lia).
    assert (NN : 0 <= Z.of_nat (length nodes)) by (clear; lia).
    assert (KD : Z.of_nat (length nodes) <= NB / 6) by (apply (A_x509_get_name_A.cnt6_div _ (p0 - P)); [exact CNT| clear - Hp2; lia]).
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
      zstep.
      rewrite (swrap32_land_errsum rv 18446744073709542528) by (clear - Hrv; lia).
      zstep.
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L26728691728.91 L59310676310.141L59310676311.14400001:01c035S2LF2sp2PP1P3END3BUF3CUR2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D11k1p2Hk2p'3Hp'S2LF2sp2PP3END3CUR1d2bs3LFB1p2Hk5nodes2H7S2LF2sp2PP1P3END3BUF3CUR1d2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D11p2Hk2es5nodes2H72H8". (* [comment removed for export] *)
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
