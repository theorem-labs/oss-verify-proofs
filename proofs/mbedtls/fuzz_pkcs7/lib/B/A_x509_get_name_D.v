(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_x509_get_name_A.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_len
     A_asn1_free_named_data_list_shallow A_crt_stmts A_crt_parse_stmts A_pkcs7_getcerts A_x509_get_name_stmt A_x509_get_name_stmtE A_x509_get_name_A A_x509_get_name_B A_x509_get_name_C.
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
    unfold A_x509_get_name_C.FSHb in FSH; try unfold A_x509_get_name_A.rsl in RSL; try unfold A_x509_get_name_A.rslr in RSL.
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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0?L10837002389.2 L12654381620.1 L13291480630.9 L1540877545.3  L1912329416.1  L22181430612.1 L23615739305.3 L24128180555.1 L25263700820.1 L27188209011.3 L31034375991.6 L32454903270.1 L39280637297.0 L50790731766.10L52045659405.3 L56523586534.1 L6203936179.1  L66084705830.9 L66151427842.16L67028235242.12L6899380056.1  L9631767084.2  00000800=00^00j00o01301=01A01E01N01a01e01f02702C02G02L02k03E03^03b03iS3BUF2bsS3BUFS1R3HIA1h4FFRx2hc2dF2h14HFRc4HFR1S2sp3sp13SP1S3sp1S2FBS1R3HIA2hcS2FBS2FBS2FB1c2HcS1R3HIA1h2sp3TOP2HTS2FBSS1R2sp2lo3SLO3LOSS2sp3sp13SP1S2FBS3sp1S1R3HIA1h4PHIx2hc2dV2h13HVc3HV1S2FB2r03F641q1r1H2H02q02H4S1R2sp2lo3SLO3LOS3sp13SP1S2FBS2FB2F0". (* [comment removed for export] *)
  #[using="IMG CWP PPLO BIN CWC CURLO SLOS SLOL SLO TOP LOS"] Lemma nvA_callF : forall r64 FB sp1 w0 w1 w2 ga gb b4 j0 j96 Lh nodes cur PHIx FFRx mc moc hc (Lh' : list blk) (dV dF : Z) m1 mo1 h1,
    nvAr r64 FB sp1 w0 w1 w2 ga gb b4 j0 j96 Lh nodes cur PHIx FFRx mc moc hc ->
    (forall b, In b LB -> In b Lh') ->
    mem_inv asegs m1 -> stk asegs m1 lo sp1 -> mo_frame moc mo1 ->
    presA asegs R LB ((FB, 128) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m1 ->
    htop asegs R HIA h1 = htop asegs R HIA hc -> hstkhi asegs R HIA h1 = hstkhi asegs R HIA hc -> hflag asegs R HIA h1 = hflag asegs R HIA hc ->
    HK asegs R HIA h1 mo1 -> (forall y, hcs asegs R HIA hc y -> hcs asegs R HIA h1 y) ->
    havol asegs R HIA h1 <= havol asegs R HIA hc + dV -> hfr asegs R HIA h1 <= hfr asegs R HIA hc + dF ->
    HM asegs R HIA h1 Lh' ((FB, 128) :: LF) m1 ->
    nvAr r64 FB sp1 w0 w1 w2 ga gb b4 j0 j96 Lh' [] CUR (PHIx + dV) (FFRx + dF) m1 mo1 h1.
  Proof.
    intros until h1. intros D SUBq MI1 ST1 MF1 HP1 HT1 HS1 HF1 HK1 HCS1 HV1 HFR1 HH1. nvA_open D. rt_facts.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT. rewrite HTc, HSc in HT.
    pose proof FRSH as FRSH'. ddestruct FRSH' as (F0 & F1 & F2 & F3).
    assert (SUBq' : forall b, In b (LB ++ fdata LF) -> In b (LB ++ fdata ((FB, 128) :: LF))).
    { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply (fdata_cons_sub b [] FB 128 LF); exact Hb]. }
    assert (CRo : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L (LB ++ fdata ((FB, 128) :: LF)) sp1 a k).
    { intros a k Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0| exact SUBq']. }
    assert (INHq : In (FB, 24) (LB ++ fdata ((FB, 128) :: LF))) by (apply in_or_app; right; cbn; left; reflexivity).
    assert (INDq : In (FB + 32, 128 - 40) (LB ++ fdata ((FB, 128) :: LF))) by (apply in_or_app; right; cbn; right; left; reflexivity).
    assert (CSHD : forall c, FB <= c < FB + 128 -> cshd R LB ((FB, 128) :: LF) (arl_stklo R) (hstkhi asegs R HIA hc) c).
    { intros c Hc. right; right; left. exists (FB, 128). split; [left; reflexivity| cbn; exact Hc]. }
    split; [exact HH1|]. split; [exact HK1|]. split; [eapply mo_frame_trans; [exact MFc| exact MF1]|].
    split; [rewrite HT1; exact HTc|]. split; [rewrite HS1; exact HSc|]. split; [rewrite HF1; exact HFc|].
    split; [intros y Hy; exact (HCS1 y (HCSc y Hy))|].
    split; [clear - HVc HV1; lia|]. split; [clear - HFRc HFR1; lia|].
    split.
    { eapply (presW_hmono R HIA hc h1); [| exact HCS1| exact HS1].
      eapply (presW_call asegs R HIA hc LB LF _ _ X0 m mc m1); [exact PRES| exact HP1| intros b Hb; exact Hb| intros b Hb; right; exact Hb
        | clear - SP1; lia| clear - LOS SLO NS1 NRT; lia| clear; lia| intros y Hy; exact I]. }
    split; [exact SP1|]. split; [exact SP1M|]. split; [exact F64|]. split; [exact FRSH|]. split; [exact CFB|].
    split; [eapply (presA_rw_cells asegs R); [exact HP1| exact FHD| cbn [cells_size csize Nat.add length]; eapply client_range_block; [exact INHq| clear; lia| clear; lia]| exact I]|].
    split; [eapply (presA_rw_cells asegs R); [exact HP1| exact GA| cbn [cells_size csize Nat.add length]; eapply client_range_block; [exact INDq| clear; lia| clear; lia]| exact I]|].
    split; [eapply (presA_rw_cells asegs R); [exact HP1| exact GB| cbn [cells_size csize Nat.add length]; eapply client_range_block; [exact INDq| clear; lia| clear; lia]| exact I]|].
    split.
    { eapply (presA_shadow_cells_sh asegs R CS); [exact CSOK| cbn [cells_size csize Nat.add length FSHb]; exact CFB| clear - F64; Z.div_mod_to_equations; lia| clear - F0; lia| exact HP1| exact FSH|].
      cbn [cells_size csize Nat.add length FSHb]. intros c Hc. apply CSHD. clear - Hc. lia. }
    split; [eapply (presA_rw_cells asegs R); [exact HP1| exact SAVE| apply client_range_stack; clear - SP1; lia| exact I]|].
    split; [eapply (presA_rw_cells asegs R); [exact HP1| exact RSL| apply client_range_stack; clear; lia| exact I]|].
    split; [eapply (presA_stk asegs R); [exact HP1| exact STb| clear; lia| exact I]|].
    split; [exact ST1|].
    split.
    { eapply (presA_bytes_at0 asegs R); [exact HP1| exact BYc|]. destruct (Nat.eq_dec (length bs) 0) as [E|NE]; [left; exact E| right].
      split; [| exact I]. eapply client_range_block; [apply in_or_app; left; exact BIN| clear; lia| clear; lia]. }
    assert (OPP1 : aobj asegs AL (hcs asegs R HIA h1) m1 PP 8).
    { eapply aobj_cs_mono; [exact HCS1|]. eapply (presA_aobj0 asegs R (hcs asegs R HIA hc)); [exact (hcs_ok asegs R HIA hc)| exact HP1| exact OPP| intros y Hy; eapply hcs_below_top; exact Hy| right; split; [apply CRo; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| clear - LOS SLO SP1 NS1 NRT; lia]]. }
    assert (OCUR1 : aobj asegs AL (hcs asegs R HIA h1) m1 CUR 64).
    { eapply aobj_cs_mono; [exact HCS1|]. eapply (presA_aobj0 asegs R (hcs asegs R HIA hc)); [exact (hcs_ok asegs R HIA hc)| exact HP1| exact OCUR| intros y Hy; eapply hcs_below_top; exact Hy| right; split; [apply CRo; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]| clear - LOS SLO SP1 NS1 NRT; lia]]. }
    split; [exact OPP1|]. split; [exact OCUR1|].
    split.
    { eapply aobj_cs_mono; [exact HCS1|]. eapply (presA_aobj0 asegs R (hcs asegs R HIA hc)); [exact (hcs_ok asegs R HIA hc)| exact HP1| exact OBUF| intros y Hy; eapply hcs_below_top; exact Hy|].
      destruct (Z.eq_dec n 0) as [E0|NE]; [left; rewrite E0; clear; lia| right]. split; [| clear - LOS SLO SP1 NS1 NRT; lia].
      eapply client_range_block; [apply in_or_app; left; exact BIN| clear; lia| clear; lia]. }
    split; [exact MI1|].
    split; [eapply (presA_sshad asegs R); [exact HP1| exact SSc| exact SLOS| rewrite HSc; clear - HT TOP; lia]|].
    split; [exact SUBq|]. split; [intros x Hx; destruct Hx|].
    split; [constructor|]. split; [intros x Hx; destruct Hx|]. split; [left; split; reflexivity|].
    split; [left; reflexivity|]. split; [exact I|].
    exact OCUR1.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L11949961375.1 L14776791339.10L2275137097.0  L27111942217.1 L34603895532.0 L35666023782.10L37156630869.0 L38691415991.0 L39332637397.0 L40228640085.0 L48132467214.11L50790731766.10L57855791009.9 L60098763854.6 L9356559676.15 00000500W00X00\00]01301401501601701V01g02F02P035S3CURS1R3HIA1h1P3END1d4FFRx2hc4HFRc3FFRSS2PPSS1R3HIA1h2sp2lo3TOP2HTSSSSS1R2sp2lo3slo4SLOS4SLOL3SLO3ALOS1R2sp2lo3SLO3LOSS1R3HIA1h1P3END4PHIx2hc3HVc3PHIS1R2lo3LOSS1R2sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPR". (* [comment removed for export] *)
  #[using="IMG LFB PP0 CWP PPLO BIN B1 B2 B3 DPB CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH LOS"] Lemma ok_exit : forall FB sp1 w0 w1 w2 ga gb b4 j0 j96 nodes cur PHIx FFRx mc moc hc (J : list byte) (MG : byte) (P7 : list byte) (p : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s3v s4v s6v s7v s8v s9v s10v s11v : word),
    nvA FB sp1 w0 w1 w2 ga gb b4 j0 j96 (nLB nodes) nodes cur PHIx FFRx mc moc hc ->
    rw_cells asegs mc cur (name_blob J 0 MG P7) ->
    rw_cells asegs mc PP [C8 (Z_to_bv 64 p)] -> P <= p <= END -> p = END ->
    Z.of_nat (length nodes) <= CNTn NB -> PHIx <= PHIn NB -> FFRx <= FFRn NB d ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      s2v s3v s4v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
                 F (Z_to_bv 64 0xad2cc) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s11v. intros D HCB PPc Hp HEND CNT PHI FFR. nvA_open D. rt_facts. walk_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NRT; lia).
    destruct (close_nodes R LB LF PP CUR FB (nLB nodes) nodes cur mc J MG P7 HFR HCF HHD SUBN HLS HCB) as [(hj & hg & hp7 & HHEAD) HLn].
    pose proof (fresh_apart_grow R HIA hc (map (fun a => (a, 64)) (rev nodes)) LB LF mc FB 128 FRSH HHc) as FRSH3.
    pose proof PRES as PRESh.
    pose proof (presW_init_at R HIA hc _ _ (nLB nodes) LF mc (bv_unsigned sp) (bv_unsigned sp) [] h HHc
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSc HSc ltac:(clear - LOS SLO NS1 NRT; lia)) as PRES2.
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hc) hc (nLB nodes) LF mc FB 128 lo HHc eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (_ & _ & _ & _ & AP & _).
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    (* [comment removed for export] *)
    zstep.
    eapply (aevtA_cut_evtA_KF asegs R HIA hc moc).
    { eapply (epi_walk R HIA) with (h := h) (lo := lo) (slo := slo) (bs := bs) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF)
                           (h3 := hc) (LBn := map (fun a => (a, 64)) (rev nodes)) (m0 := m) (m2x := mc) (WA := X0) (WB := []) (b8 := Z_to_bv 8 0) (r64 := -10368);
        first [ sec_hyps | exact HHc | exact HCSc | exact PRESh | exact PRES2 | exact CFB | exact FRSH3 | exact AP
              | lazymatch goal with
                | |- rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ => exact FSH
                | |- - 2 ^ 31 < 0 < 2 ^ 31 => clear; lia
                | |- rw_cells _ _ _ (A_x509_get_name_A.rslr _ _ _ _ _ _) => unfold A_x509_get_name_A.rslr; exact RSL
                end
              | eassumption | reflexivity
              | match goal with |- ?g => idtac "OK-EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    ddestruct EP as (m9 & h4 & z0 & z1 & z2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6
                    & -> & MI9 & ST9 & SS9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    pose proof (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES29) as HP29.
    assert (CRsp : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L (nLB nodes ++ fdata LF) (bv_unsigned sp) a k).
    { intros a k Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0|].
      intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply nLB_sub; exact Hb| right; exact Hb]. }
    unfold x509_get_name_postE.
    deexists 15. dexists m9, mo9, h4, 0, p, hj, hg, hp7, nodes.
    split; [reflexivity|].
    split; [reflexivity|]. split; [clear; lia|].
    split; [exact MI9|]. split; [exact ST9|]. split; [exact SS9|]. split; [eapply mo_frame_trans; [exact MFc| exact MF9]|].
    split.
    { pose proof (presW_presA asegs R HIA hc LB LF _ _ _ _ _ PRES9) as HPF. rewrite HSc in HPF. unfold NAME_SIZE. exact HPF. }
    split; [rewrite E4top; exact HTc|]. split; [rewrite E4stk; exact HSc|]. split; [rewrite E4flag; exact HFc|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSc x Hx)|].
    split; [rewrite E4vol; clear - HVc PHI; lia|].
    split; [rewrite E4fr; clear - HFRc FFR; lia|].
    split; [exact CNT|].
    split; [eapply (presA_rw_cells asegs R); [exact HP29| exact PPc| apply CRsp; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| exact I]|].
    split; [exact Hp|].
    split; [eapply (presA_rw_cells asegs R); [exact HP29| exact HHEAD| cbn [cells_size csize Nat.add length name_blob]; apply CRsp; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]| exact I]|].
    split.
    { change (SNAME (rev nodes) ++ LB) with (nLB nodes). apply name_lseg_chain.
      eapply (lseg_presA R (nLB nodes) LF (bv_unsigned sp)); [exact HP29| intros x Hx; apply SUBN; exact Hx| clear - ALO LOS SLO NS1 NRT; lia| exact HLn]. }
    split; [exact HND|].
    split; [intros x Hx B k Hb; unfold NAME_SIZE; ddestruct (HFR x Hx) as (_ & _ & _ & _ & NAP & _); apply NAP; apply in_or_app; left; exact Hb|].
    split; [exact HH4|].
    split; [intros NE; exfalso; exact (NE eq_refl)| intros _; exact HEND].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0160@D4169524348.239 D59892785054.239D60109196847.239K20177394750.239K20957767126.239K25746690853.239K32859452709.239K44164039966.239L11949961375.1  L11972929557.12 L1685717371.0   L19980016842.7  L20171099480.2  L20970438176.2  L2275137097.0   L25742411987.2  L27111942217.1  L32855174867.2  L34745960310.10 L35666023782.10 L37156630869.0  L37296633443.198L3778745608.10  L39332637397.0  L40228640085.0  L42506209623.2  L43090580551.2  L44168742175.3  L45354782925.2  L45491845428.4  L46938023093.8  L47427904289.0  L49152796133.11 L49493397620.5  L50790731766.10 L52895316838.2  L59308660947.3  L60098763854.6  L66151427842.16 L66734300828.10 L67216882861.11 L9356559676.15  P42504116273.239P45360812554.239Q27632138441.205Q27646900137.235Q33354927453.206Q33354927453.236Q37989833245.205Q40730279609.206Q4169524348.239 Q4171705980.238 Q42439443119.239Q46184984384.239Q47131700614.206Q47131700614.236Q54618242077.206Q56420723160.236Q59865321072.239Q59890570654.238Q59892785054.239Q6040596876.235 Q6052921817.206 Q6052921817.236 Q6055460588.205 Q63025202418.237Q64683667846.239Q66559811968.205Q9787947837.235 Q9790223453.205 00000c01V02P03<03i04V05C06106606c06d07<07=07>07?07@07D07E07U07k07l09609[09\09]09^09d09e09f0:00:I0:J0;30;=0;N0;T0;]0;g0<C0<Q0=90=^0>T0?R0?i0@@0@W0@n0AO0AP0B60B\0CK0CL0DI0EF0EG0Ef0Eg0FM0G30GJ0Ga0H80HO0Ho0Ii0JN0Je0K<S1R2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes2HB5Ha_st5Hl_stS1R2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes2HB5Ha_st5Hl_stS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes2HB5Ha_st5Hl_stS1R2LF2PP3CUR2bs3LFB2D15nodes2HB5Ha_st5Hl_stS1R2LF3CUR2bs3LFB2FB5nodes3APC2HB5Ha_st5Hl_stS1R2LF3CUR2bs3LFB2FB5nodes3APC2HB5Ha_st5Hl_stS1R2LF3CUR2bs3LFB2FB5nodes3APC2HB5Ha_st5Hl_stS1R2LF3BUF3CUR2bs3LFB3DCB5nodes2HB5Ha_st5Hl_stS3CURS1R3HIA1h1P3END1d5nodes4FFRx2hc4HFRc3FFR4BUDFSS1R3HIA1h2sp3TOP3sp13SP1FFSFS2PPFS1R3CUR2lo5CURLOS1R3HIA1h2sp2lo3TOP2HTSS1R2LF2sp2PP3CUR2lo2bs3LFB3PP04CUR05CURLO3SLO3SPH2FB3sp15nodes3SPR2F04SP1RS1R3HIA1h1P3END5nodes4PHIx3PHI2h23HVcSSFS1r2HrFFS1P3END2B2S1R3NRT2sp2lo3SLO3sp13SP1SS1R3HIA1h1P3END5nodes4PHIx2hc3HVc3PHI3BUDS1P3END2B2S1R2sp2lo3SLO3LOSS1r2HrS1r2Hr2E0S1R2lo3LOSS3sp12r04SP1M1q1r1H2H02q02H4S1R2PP2lo4PPLOS1R3HIA1h1P3END1d5nodes4FFRx3FFR2h24HFRcS1R2sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R2LF2sp3CUR2lo2bs3LFB5CURLO3SLO5nodes2HB5Ha_st5Hl_stS1R2LF2sp3CUR2lo2bs3LFB5CURLO3SLO3sp15nodes3SP12HB5Ha_st5Hl_stS1R2LF3CUR2bs3LFB5nodesS1R2LF3CUR2bs3LFB5nodesS1R2LF3CUR2bs3LFB5nodesS1R2LF3CUR2bs3LFB5nodesS1R2LF2sp2lo2bs3LFB3sp15nodes3SP1FS1R2LF3CUR2bs3LFB5nodes2HB5Ha_st5Hl_stS1R2LF3CUR2bs3LFB5nodes2HB5Ha_st5Hl_stS1R2LF3CUR3slo2bs3LFB4SLOS5nodes2HB5Ha_st5Hl_stFS1R2LF2sp2PP3CUR2bs3LFB3PP03ALC4CUR02FB3sp15nodes3SPR2F04SP1RS1R2LF2sp2PP3CUR2bs3LFB3PP03ALC4CUR02FB3sp15nodes3SPR4SP1R2F0FS1R2LF3CUR2bs3LFB4CUR05nodes2HBFS1R2LF3CUR2bs3LFB5nodes2HB5Ha_st5Hl_stS1R2LF3CUR2bs3LFB5nodes2HB5Ha_st5Hl_stS1R2LF3CUR2bs3LFB5nodesS1R2LF3CUR2bs3LFB5nodesS1R2LF3CUR2bs3LFB5nodesS1R2LF3CUR2bs3LFB5nodesS1R2LF3CUR2bs3LFB5nodes2HB5Ha_stS1R3HIA1h2LF2sp3CUR3slo2bs3LFB3TOP5nodes2HT2HB5Ha_st5Hl_stS1R2LF2sp2lo2bs3LFB3SLO3sp15nodes3SP1S1R2LF3CUR2bs3LFB5nodesS1R2LF3CUR2bs3LFB5nodes". (* [comment removed for export] *)
  #[using="IMG FREEL NRT LFB PP0 CWP PPLO BIN B1 B2 B3 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH TPV LOS"] Lemma err_exit : forall FB sp1 w0 w1 w2 ga gb b4 j0 j96 nodes cur PHIx FFRx mc moc hc (J : list byte) (MG : byte) (P7 : list byte) (p r : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s3v s4v s6v s7v s9v s10v s11v : word),
    nvAr r FB sp1 w0 w1 w2 ga gb b4 j0 j96 (nLB nodes) nodes cur PHIx FFRx mc moc hc ->
    rw_cells asegs mc cur (name_blob J 0 MG P7) ->
    rw_cells asegs mc PP [C8 (Z_to_bv 64 p)] -> P <= p <= END ->
    PHIx + Z.of_nat (length nodes) * AVOL_CALL <= PHIn NB -> FFRx + Z.of_nat (length nodes) * fr_charge 0 <= FFRn NB d ->
    havol asegs R HIA h + PHIn NB <= AVOL_MAX -> hfr asegs R HIA h + FFRn NB d <= FR_MAX ->
    -0x3000 < r < 0 ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      s2v s3v s4v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) s6v s7v (Z_to_bv 64 (al_sb AL)) s9v s10v s11v t3 t4 t5 t6)
                 F (Z_to_bv 64 0xad184) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s11v. intros D HCB PPc Hp PHI FFR BUD BUDF Hr. pose proof D as D0. nvA_open D. rt_facts. walk_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NRT; lia).
    destruct (close_nodes R LB LF PP CUR FB (nLB nodes) nodes cur mc J MG P7 HFR HCF HHD SUBN HLS HCB) as [(hj & hg & hp7 & HHEAD) HLn].
    pose proof (name_lseg_chain asegs mc (nLB nodes) nodes HLn) as HNC.
    clear HCB HHD HLS.
    unfold name_blob in HHEAD.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep.
    pose proof FREEL as FL'. unfold asn1_free_named_data_list_shallow_stmtA, A_ASN1_FREE_NAMED_DATA_LIST_SHALLOW in FL'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply FL' with (h := hc) (LB := nLB nodes) (LF := (FB, 128) :: LF) (a := hd 0 nodes) (nodes := nodes) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HHc | exact HK1 | exact HNC | exact HND | exact LOS | exact TPV | exact MIc
              | lazymatch goal with
                | |- stk _ _ lo _ => exact STlo
                | |- lo <= sp1 - _ - _ => clear - SLO SP1 NS1 NRT; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD PHI HVc; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDF FFR HFRc; lia
                | |- _ = Z_to_bv 64 (hd 0 nodes) => reflexivity
                end
              | match goal with |- ?g => idtac "FREEL-PRE-LEFT:" g end ]. }
    clear FL'.
    cbv beta. (intros ms2 mo2x dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    unfold asn1_free_named_data_list_shallow_postA in PO.
    ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & mo2 & h2 & E2 & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2).
    injection E2 as Ems Emo. subst ms2 mo2x.
    rewrite ?(unsigned_lit sp1) in ST2 by exact SP1R. rewrite ?(unsigned_lit sp1) in HP2 by exact SP1R.
    unfold A_x509_get_name_C.nLB in HP2, HH2. rewrite (lb_remove_all_new nodes LB HND) in HP2, HH2.
    lazymatch goal with |- _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
    (* [comment removed for export] *)
    assert (HHEAD2 : rw_cells asegs m2 CUR [CB 48 hj; C8 (Z_to_bv 64 (hd 0 nodes)); C1 hg; CB 7 hp7]).
    { eapply (presA_rw_cells asegs R); [exact HP2| exact HHEAD| | exact I]. cbn [cells_size csize Nat.add length].
      eapply (client_range_lower L _ lo); [| clear - CURLO SLO SP1 NS1 NRT; lia]. eapply client_range_incl; [exact (client_range_of_w L _ _ _ _ _ CWC)|].
      intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply (fdata_cons_sub b [] FB 128 LF); exact Hb]. }
    assert (PPc2 : rw_cells asegs m2 PP [C8 (Z_to_bv 64 p)]).
    { eapply (presA_rw_cells asegs R); [exact HP2| exact PPc| | exact I]. cbn [cells_size csize Nat.add length].
      eapply (client_range_lower L _ lo); [| clear - PPLO SLO SP1 NS1 NRT; lia]. eapply client_range_incl; [exact (client_range_of_w L _ _ _ _ _ CWP)|].
      intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply (fdata_cons_sub b [] FB 128 LF); exact Hb]. }
    assert (D2 : nvAr r FB sp1 w0 w1 w2 ga gb b4 j0 j96 LB [] CUR (PHIx + Z.of_nat (length nodes) * AVOL_CALL) (FFRx + Z.of_nat (length nodes) * fr_charge 0) m2 mo2 h2).
    { eapply (nvA_callF r FB sp1 w0 w1 w2 ga gb b4 j0 j96 (nLB nodes) nodes cur PHIx FFRx mc moc hc LB); first [exact D0 | intros b Hb; exact Hb | exact (mo_frame_trans _ _ _ MF1 MF2) | eassumption]. }
    clear D0 HHc HKc MFc HTc HSc HFc HCSc HVc HFRc PRES SP1 SP1M F64 FRSH CFB FHD GA GB FSH SAVE RSL STb STlo BYc OPP OCUR OBUF MIc SSc
          SUBL SUBN HND HFR HCF OCc HHEAD PPc HNC HP2 HH2 MI2 ST2
          CSOKc HT CFBc SCS03c SCS SCSc CRP CRC APP APC F0 F1 F2 F3 APB STKH WL WCC WCP CWCc CWPc.
    pose proof D2 as D0. nvA_open D2. walk_prep.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo2) _ _ _ (conj HKc (mo_frame_refl mo2))).
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    (* [comment removed for export] *)
    lazymatch goal with PR : presW _ _ _ h2 LB LF _ _ _ m m3 |- _ => pose proof PR as PRESh end.
    lazymatch goal with HH3 : HM _ _ _ h2 LB _ m3 |- _ =>
      pose proof (presW_init_at R HIA h2 _ _ LB LF m3 (bv_unsigned sp) (bv_unsigned sp) [] h HH3
                    ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSc HSc ltac:(clear - LOS SLO NS1 NRT; lia)) as PRES2;
      ddestruct (frame_factsA R HIA (hcs asegs R HIA h2) h2 LB LF m3 FB 128 lo HH3 eq_refl FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (_ & _ & _ & _ & AP & _);
      eapply (aevtA_cut_evtA_KF asegs R HIA h2 mo2);
      [ eapply (epi_walk R HIA) with (h := h) (lo := lo) (slo := slo) (bs := bs) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF)
                           (h3 := h2) (LBn := []) (m0 := m) (m2x := m3) (WA := X0) (WB := []) (b8 := Z_to_bv 8 0) (r64 := r);
        first [ sec_hyps | exact HH3 | exact HCSc | exact PRESh | exact PRES2 | exact CFB | exact AP
              | lazymatch goal with
                | |- rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ => exact FSH
                | |- fresh_apart _ ([] ++ LB) LF FB 128 => exact FRSH
                | |- - 2 ^ 31 < r < 2 ^ 31 => clear - Hr; lia
                | |- rw_cells _ _ _ (A_x509_get_name_A.rslr _ _ _ _ _ _) => unfold A_x509_get_name_A.rslr; eassumption
                end
              | eassumption | reflexivity
              | match goal with |- ?g => idtac "ERR-EPI-PRE-LEFT:" g end ] |] end.
    cbv beta. intros ms9 EP.
    ddestruct EP as (m9 & h4 & z0 & z1 & z2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6
                    & -> & MI9 & ST9 & SS9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    pose proof (presW_presA asegs R HIA h2 _ LF _ _ _ _ _ PRES29) as HP29. cbn [app] in HP29.
    assert (CRsp : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L (LB ++ fdata LF) (bv_unsigned sp) a k).
    { intros a k Hk CR0. eapply client_range_lower; [exact CR0| exact Hk]. }
    unfold x509_get_name_postE.
    lazymatch goal with HD3 : rw_cells _ m3 CUR [CB 48 hj; _; C1 hg; CB 7 hp7] |- _ => rename HD3 into HHEAD3 end.
    deexists 15. dexists m9, mo9, h4, r, p, hj, hg, hp7, [].
    split; [reflexivity|].
    split; [reflexivity|]. split; [clear - Hr; lia|].
    split; [exact MI9|]. split; [exact ST9|]. split; [exact SS9|]. split; [eapply mo_frame_trans; [exact MFc| exact MF9]|].
    split.
    { pose proof (presW_presA asegs R HIA h2 LB LF _ _ _ _ _ PRES9) as HPF. rewrite HSc in HPF. unfold NAME_SIZE. exact HPF. }
    split; [rewrite E4top; exact HTc|]. split; [rewrite E4stk; exact HSc|]. split; [rewrite E4flag; exact HFc|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSc x Hx)|].
    split; [rewrite E4vol; clear - HVc PHI; lia|].
    split; [rewrite E4fr; clear - HFRc FFR; lia|].
    split; [cbn [length Z.of_nat]; pose proof (CNTn_mono 0 NB ltac:(clear - B1 B2; lia)); unfold A_x509_get_name_A.CNTn in *; clear - H B2; lia|].
    split; [eapply (presA_rw_cells asegs R); [exact HP29| eassumption| apply CRsp; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| exact I]|].
    split; [exact Hp|].
    split; [cbn [hd]; unfold name_blob; eapply (presA_rw_cells asegs R); [exact HP29| exact HHEAD3| cbn [cells_size csize Nat.add length]; apply CRsp; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]| exact I]|].
    split; [cbn; reflexivity|].
    split; [constructor|].
    split; [intros x Hx; destruct Hx|].
    split; [exact HH4|].
    split; [intros _; reflexivity| intros E0; exfalso; clear - E0 Hr; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="IMG FREEL NRT LFB PP0 CWP PPLO BIN B1 B2 B3 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH TPV LOS"] Lemma err_exit0 : forall FB sp1 w0 w1 w2 ga gb b4 j0 j96 nodes cur PHIx FFRx mc moc hc (J : list byte) (MG : byte) (P7 : list byte) (p : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s3v s4v s6v s7v s9v s10v s11v : word),
    nvA FB sp1 w0 w1 w2 ga gb b4 j0 j96 (nLB nodes) nodes cur PHIx FFRx mc moc hc ->
    rw_cells asegs mc cur (name_blob J 0 MG P7) ->
    rw_cells asegs mc PP [C8 (Z_to_bv 64 p)] -> P <= p <= END ->
    PHIx + Z.of_nat (length nodes) * AVOL_CALL <= PHIn NB -> FFRx + Z.of_nat (length nodes) * fr_charge 0 <= FFRn NB d ->
    havol asegs R HIA h + PHIn NB <= AVOL_MAX -> hfr asegs R HIA h + FFRn NB d <= FR_MAX ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      s2v s3v s4v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) s6v s7v (Z_to_bv 64 (al_sb AL)) s9v s10v s11v t3 t4 t5 t6)
                 F (Z_to_bv 64 0xad184) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s11v. intros D HCB PPc Hp PHI FFR BUD BUDF.
    exact (err_exit FB sp1 w0 w1 w2 ga gb b4 j0 j96 nodes cur PHIx FFRx mc moc hc J MG P7 p (-10368)
             xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s3v s4v s6v s7v s9v s10v s11v
             D HCB PPc Hp PHI FFR BUD BUDF ltac:(clear; lia)).
  Qed.
  End Call.
End Walk.
