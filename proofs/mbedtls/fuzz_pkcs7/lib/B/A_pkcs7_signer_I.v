(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_pkcs7_signer.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag
     A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt A_pkcs7_signer_A A_pkcs7_signer_B A_pkcs7_signer_C A_pkcs7_signer_D A_pkcs7_signer_E A_pkcs7_signer_F A_pkcs7_signer_G A_pkcs7_signer_H
     A_pkcs7_getsig_A A_asn1_get_alg_null_A A_x509_get_name_stmt A_x509_get_serial A_asn1_get_int_loops A_pkcs7_signers_A A_pkcs7_signers_C A_pkcs7_signers_D A_pkcs7_signers_G.
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
Definition A_WFREE : Z := 0x6947c.                (* [comment removed for export] *) (* [comment removed for export] *)

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x993cc]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis CALLOC : arl_calloc R = A_WCALLOC.
  Hypothesis FREE : arl_free R = A_WFREE.
  (* [comment removed for export] *)
  Hypothesis GETTAG : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_G.
  (* [comment removed for export] *)
  Variables (PHIn : Z -> Z) (FFRn : Z -> Z -> Z) (CNTn : Z -> Z) (STKn : Z).
  Hypothesis STKn0 : 0 <= STKn.
  Hypothesis PHIn_mono : forall n n', 0 <= n <= n' -> 0 <= PHIn n <= PHIn n'.
  Hypothesis FFRn_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRn n d <= FFRn n' d.
  Hypothesis CNTn_mono : forall n n', 0 <= n <= n' -> 0 <= CNTn n <= CNTn n'.
  Hypothesis GETSIG : pkcs7_getsig_stmtA asegs R HIA A_PKCS7_GETSIG.
  Hypothesis ALGNULL : asn1_get_alg_null_stmtA asegs R HIA A_ASN1_GET_ALG_NULL.
  Hypothesis MCI : arl_memcmp_i R = 0x58704.   (* [comment removed for export] *)
  Hypothesis NBC : 0 <= arl_need_bcmp R.
  Hypothesis GETNAME : x509_get_name_stmtA asegs R HIA PHIn FFRn CNTn STKn A_X509_GET_NAME.
  Hypothesis SERIAL : x509_get_serial_stmtA (L := L) asegs AL A_X509_GET_SERIAL.
  Hypothesis GETINT : asn1_get_int_stmtA (L := L) asegs AL A_ASN1_GET_INT_G.
  Hypothesis NAM0 : 0 <= arl_need_amem R.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55857805827.27000003S1R". (* [comment removed for export] *)
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition STKsg : Z := 208 + Z.max (Z.max STKn 4208) (Z.max (304 + arl_need_amem R) (Z.max (112 + arl_need_smalloc R) (Z.max (arl_need_rt R) (arl_need_bcmp R)))).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP P END BUF SIG DALG lo slo d : Z) (bs : list byte) (dtg dpad : word) (dlen dq : Z) (sj : signer_junk).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 2)%nat.
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
  Hypothesis HSG : rw_cells asegs m SIG (signer_cells 0 0 sj).
  Hypothesis ALS : SIG mod 8 = 0.
  Hypothesis SG0 : 0 < SIG.
  Hypothesis CWS : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) SIG SIGNER_SIZE.
  Hypothesis SGLO : SIG + SIGNER_SIZE <= lo.
  Hypothesis DSB : SIG + SIGNER_SIZE <= BUF \/ BUF + n <= SIG.
  Hypothesis HDA : rw_cells asegs m DALG (buf_cells dtg dpad dlen dq).
  Hypothesis ALD : DALG mod 8 = 0.
  Hypothesis DA0 : 0 < DALG.
  Hypothesis CRDA : client_range L (LB ++ fdata LF) lo DALG 24.
  Hypothesis DALO : DALG + 24 <= lo.
  Hypothesis Q1 : BUF <= dq. Hypothesis Q2 : 0 <= dlen. Hypothesis Q3 : dq + dlen <= BUF + n.
  Hypothesis D1 : PP + 8 <= SIG \/ SIG + SIGNER_SIZE <= PP.
  Hypothesis D2 : PP + 8 <= DALG \/ DALG + 24 <= PP.
  Hypothesis D3 : DALG + 24 <= SIG \/ SIG + SIGNER_SIZE <= DALG.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKsg.
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
    unfold A_pkcs7_cinfo.A_UAR_GOT, A_fuzz_entry.A_UAR_GOT in UARG; unfold A_SMALLOC_0 in SM0; unfold STKsg in SLO; unfold SIGNER_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation FSH0 :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].


  Local Notation CNTsi := (A_pkcs7_signer_C.CNTsi CNTn).
  Local Notation PHIsi := (A_pkcs7_signer_C.PHIsi PHIn CNTn).
  Local Notation FFRsi := (A_pkcs7_signer_C.FFRsi FFRn CNTn).
  Local Notation NB := (END - P).
  Local Notation POST := (pkcs7_signer_postA asegs R HIA PHIsi FFRsi CNTsi h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP P END SIG NB lo slo d m mo0).
  Local Notation X0 := [(PP, PP + 8); (SIG, SIG + 200)].
  Local Notation gvA := (gvA R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP P END BUF SIG DALG lo slo bs dtg dpad dlen dq).
  Ltac gvA_open D :=
    destruct D as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & PRES & SP1 & SP1M & F64 & FRSH & CFB
                   & FHD & G4 & FSH & SAVE & RSL & STb & STlo & PPc & Hpc & CSG & SZC & DAc & BYc & OPP & OSG & ODA & OBUF & MIc & SSc).
  Local Notation gvS := (A_pkcs7_signer_C.gvS R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP P END BUF SIG DALG lo slo bs dtg dpad dlen dq).
  Ltac gvS_open D :=
    destruct D as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & PRES & SP1 & SP1M & F64 & FRSH & CFB
                   & FHD & G4 & FSH & SAVE & RSL & STb & STlo & PPc & Hpc & CSG & SZC & DAc & BYc & OPP & OSG & ODA & OBUF & MIc & SSc).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L38885538412.800000BS1R4STKn2sp2lo3SLO". (* [comment removed for export] *)
  Let SLOq : lo <= bv_unsigned sp - A_pkcs7_signers_A.STKs R STKn.
  Proof. unfold A_pkcs7_signers_A.STKs. unfold STKsg in SLO. clear - SLO NS1 NAM0 STKn0. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac sec_hyps :=
    first [ exact IMG | exact UARG | exact SM0 | exact NS1 | exact DIMG | exact HMND | exact CALLOC | exact FREE | exact STKn0 | exact NAM0 | exact GETSIG | exact ALGNULL | exact MCI | exact NBC | exact GETNAME | exact SERIAL | exact GETINT | exact GETTAG
          | exact PHIn_mono | exact FFRn_mono | exact CNTn_mono
          | exact LFB | exact HPP | exact ALP | exact PP0 | exact CWP | exact PPLO | exact HBY | exact BIN | exact B1 | exact B2 | exact B3 | exact B47 | exact B5 | exact B30 | exact DPB
          | exact HSG | exact ALS | exact SG0 | exact CWS | exact SGLO | exact DSB | exact HDA | exact ALD | exact DA0 | exact CRDA | exact DALO | exact Q1 | exact Q2 | exact Q3
          | exact D1 | exact D2 | exact D3 | exact SLOS | exact SLOL | exact SLO | exact SLOq | exact TOP | exact SPA | exact SPH | exact TPV | exact NDL ].

  Ltac walk_prep :=
    lazymatch goal with HHc : HM _ _ _ ?hc (?Lc ++ LB) ((?FB, 64) :: LF) ?mc, HTc : htop _ _ _ ?hc = _, HSc : hstkhi _ _ _ ?hc = _, HCSc : forall x, CS x -> hcs _ _ _ ?hc x,
                        CFB : crange CS ?FB 64, FRSH : fresh_apart R LB LF ?FB 64, OPP : aobj _ _ CS ?mc PP 8, OSG : aobj _ _ CS ?mc SIG 200, ODA : aobj _ _ CS ?mc DALG 24,
                        PRES : presW _ _ _ h LB LF _ _ _ m ?mc, SCS0 : crange CS (arl_stklo R) _ |- _ =>
      pose proof (hcs_ok asegs R HIA hc) as CSOKc;
      pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT; rewrite HTc, HSc in HT;
      pose proof (crange_mono _ _ _ _ HCSc CFB) as CFBc;
      pose proof (crange_mono _ _ _ _ HCSc SCS0) as SCS03c;
      assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 NAM0 STKn0 NRT TOP HT; lia]);
      pose proof (crange_mono _ _ _ _ HCSc SCS) as SCSc;
      pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OPP) as OPPc;
      pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OSG) as OSGc;
      pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc ODA) as ODAc;
      pose proof OPP as CRP; apply aobj_crange in CRP; pose proof OSG as CRS; apply aobj_crange in CRS; pose proof ODA as CRDg; apply aobj_crange in CRDg;
      pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 64 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP;
      pose proof (frame_apart_obj R HIA LB LF lo _ SIG 200 FB 64 FRSH CWS ltac:(clear; lia) ltac:(clear; lia) LOS) as APSG;
      pose proof FRSH as FRSH'; unfold fresh_apart in FRSH'; destruct FRSH' as (F0 & F1 & F2 & F3);
      pose proof (art_stk_high asegs R HIA) as STKH;
      assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]);
      assert (WCS : wcover R LB LF (bv_unsigned sp) X0 SIG 200) by (apply wcover_inside; cbn [inside]; right; left; clear; lia);
      assert (WCP : wcover R LB LF (bv_unsigned sp) X0 PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia);
      assert (CWSc : client_wrange L ((Lc ++ LB) ++ fdata ((FB, 64) :: LF)) lo (htop asegs R HIA hc) SIG 200)
        by (rewrite HTc; eapply client_wrange_mono; [exact CWS|]; intros b Hb; apply in_app_iff in Hb; apply in_app_iff;
            destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb| right; apply (fdata_cons_sub b [] FB 64 LF); exact Hb]);
      assert (CWPc : client_wrange L ((Lc ++ LB) ++ fdata ((FB, 64) :: LF)) lo (htop asegs R HIA hc) PP 8)
        by (rewrite HTc; eapply client_wrange_mono; [exact CWP|]; intros b Hb; apply in_app_iff in Hb; apply in_app_iff;
            destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb| right; apply (fdata_cons_sub b [] FB 64 LF); exact Hb])
    end.

  Ltac gvA_fin HK9 MFc MF9 :=
    lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signer_C.gvS] => idtac end end;
    lazymatch goal with HTc : htop _ _ _ ?hc = _, HSc : hstkhi _ _ _ ?hc = _, HFc : hflag _ _ _ ?hc = _, HCSc : forall x, CS x -> hcs _ _ _ ?hc x,
                        HVc : havol _ _ _ ?hc <= _, HFRc : hfr _ _ _ ?hc <= _ |- _ =>
      split; [cbn [app]; eassumption|]; split; [exact HK9|]; split; [eapply mo_frame_trans; [exact MFc| exact MF9]|];
      split; [exact HTc|]; split; [exact HSc|]; split; [exact HFc|]; split; [exact HCSc|]; split; [exact HVc|]; split; [exact HFRc|];
      split; [eassumption|];
      repeat match goal with |- _ /\ _ => split end;
      first [ eassumption | reflexivity
            | match goal with H : ?a <= ?x <= ?b |- ?a' <= ?x' => first [exact (proj1 H) | exact (proj2 H)] end
            | match goal with |- ?g => idtac "GVA-FIN-LEFT:" g end ]
    end.

  Ltac seg2_pc_is t :=
    lazymatch goal with |- context [MS _ _ (Z_to_bv 64 ?pc) _ _ _ _] =>
      lazymatch eval vm_compute in (Z.eqb pc t) with true => idtac | false => fail 1 "SEG2: pc differs from" t end end.

  Local Notation SC := A_pkcs7_signer_D.SC.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L18171637480.1L33965478404.2L61055709130.000000300900:S1rS1r2HrS". (* [comment removed for export] *)
  #[using="Type"] Lemma mod64_neg_small : forall r, -2^63 < r < 0 -> r mod 2 ^ 64 = r + 2 ^ 64.
  Proof. clear - HIA. intros r Hr. rewrite <- (Z.mod_add r 1 (2 ^ 64)) by (clear; lia). rewrite Z.mod_small by (clear - Hr; lia). clear; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Notation S1P := (A_pkcs7_signer_A.S1P R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP P END BUF SIG DALG lo slo bs dtg dpad dlen dq sj).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03D0@C40858145355.278C51190736507.279D10636937134.279D16071854214.279D16901939902.279D18513027960.279D3953997537.256 D46794843979.279D60109446735.279D60189065437.256D61006130704.279K20981739667.277K2996319277.279 K30993319891.279K34672375905.279K41574204919.279K48171199513.279K53642109465.279K61352445407.277K62454166500.277K65858155712.277L10914754091.7  L11328261952.5  L12126572370.2  L12258921699.3  L12790317110.2  L15756354262.7  L1685717371.0   L17842793414.9  L18435658628.3  L18930958230.3  L20977711877.2  L21654730866.2  L22006224440.9  L23701062899.3  L24830734508.268L2621559066.1   L27111942217.1  L27940405558.11 L28632618922.2  L28921212824.269L29923625174.3  L2996648112.2   L30507144274.2  L30997223346.3  L31496659835.1  L33092060257.269L34561812625.3  L34563789585.3  L34603895532.0  L34666100604.2  L35666023782.13 L36012960645.4  L36054419954.2  L36215445782.9  L37232046390.2  L38235734261.1  L38259954321.2  L38308634325.0  L39263166881.0  L39332637397.0  L40228640085.0  L40391753360.3  L41202929119.246L41587086742.3  L42927756920.1  L44166924249.3  L46860880206.245L46887489569.8  L4713762890.2   L47278783245.1  L47870616696.2  L48171524228.2  L48811905840.1  L48946950765.3  L49493397620.5  L50678314462.3  L50925318027.2  L51172829802.3  L53246993999.2  L53506585793.266L53617080676.3  L53648387332.2  L55308160635.3  L56380991837.10 L576250137.246  L57698627611.2  L58972524609.3  L59425632820.269L59579494296.269L59589546465.266L60098763854.6  L61016596749.1  L61339700809.2  L62449743986.2  L62560708162.2  L63324447008.1  L64179129035.1  L65862516566.2  L66151427842.16 L66298372189.2  L66812728480.3  L67070089790.2  L67653551064.2  L881835912.0    L9080220944.4   L9356559676.18  O11883391455.279O14912726833.279O18988691132.277O22525005962.277O251358926.277  O25522832421.279O33711877170.277O3493317847.277 O36081036635.277O37559489567.279O3821773283.279 O39006531723.279O44938202843.277O45108703401.276O49442738117.276O50011839873.277O52099334849.279O55209884805.277O56225203089.277O64474006218.277O65199813233.279O65961212488.277O66321155265.279O67337474427.279O7941232487.279 P12115299733.256P12795822833.256P28627113325.256P30511339222.277P36069579605.279P37243319281.256P38261788758.256P40389176375.276P44164039966.256P4699620077.279 P47876372191.277P50671478649.277P50927926572.277P51183859917.277P53236492626.277P53607099331.276P57713046236.256P62545491173.279P66292560634.277P66818508295.279P67064334489.279Q10598857381.253Q10636937134.279Q10649498890.254Q10651584438.253Q13732682891.253Q17027695041.279Q17681074618.279Q17701933584.254Q18513027960.279Q21767670690.279Q21845213585.279Q21925682067.252Q24675662777.277Q26278822586.277Q27458512306.256Q27573751300.279Q27942454161.279Q2803826605.279 Q28465177121.253Q29148562719.279Q29775981542.279Q29986817794.277Q32681607669.279Q32681824661.256Q33137450695.279Q3419689062.256 Q3421936230.255 Q3534023209.276 Q37149073081.256Q38155417133.276Q38167875878.256Q39180574961.256Q39600066516.254Q42439168719.279Q42439443119.256Q45353866761.253Q46794843979.279Q50294161588.253Q5265442331.254 Q53380958617.254Q55415036769.256Q56854244147.256Q57228775306.255Q57230951818.256Q59865321072.256Q59865603600.279Q60071281945.254Q61006130704.279Q61018365366.276Q61018676404.277Q61847600945.254Q61951113475.279Q61957894121.279Q64683667846.256Q64683942374.279Q67023636020.277Q7522361358.252 Q9356757127.256 Q9644583048.279 00000400902R05R08X0;10>F0@_0C?0FN0Hg0K]0Ml0P>0RK0TZ0Vl0Y90\00^g0a]0b60bG0bH0bT0bU0bc0bd0c20c?0c@0cA0cB0cQ0c\0f90f>0fB0f\0f]0i60iA0iB0iC0iD0iI0kb0km0l80l90l:0lU0le0lf0m80m90m=0m>0m?0m@0mA0mB0mC0o\0o]0ob0oc12i13E13F13K13L13M13N13V13`13a13b13c13d16=16>16?16G16`19919:19F19G1;`1>91>C1>H1>I1>J1>K1>P1>Q1>R1?61?71?81?91?A1?B1?Q1@@1@A1@B1@C1@D1@E1@F1@G1@H1@I1@J1@K1@L1@M1@N1@O1@P1@Q1@k1@l1@m1@n1@o1A01A11A21Cg1FY1IT1Km1NK1Q=1T81VV1YS1\11^X1`n1cU1eh1h>1j_1mE1oh22:24c27D29N2;X2=b2?l2B62D@2Fa2Hk2K22MS2MT2Om2On2Rc2UU2UV2Wo2Z:2\M2^T2`f2bm2bn2bo2eD2gm2jV2l]2oR31Y31Z34O34P36`39H3;R3=\3?f3B:3B;3Da3Db3GO3J<3J=3J>3J?3LF3NM3PT3SA3SB3U`3XS3Zn3Zo3]D3_T3aaS2PPS3SIGS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SPR2F04SP1R3SGBS1R3HIA4STKn1h2LF2sp2PP3SIG4DALG2bs3LFB3PP03SG03DA03TOP2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02hc3HTc3SP13SZC3SPR2F04SP1R3SGBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R3HIA4STKn1h2LF2sp2PP3SIG4DALG2bs3LFB3PP03SG03DA03TOP2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02hc3HTc3SP13SZC3SPR2F04SP1R3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SPR2F04SP1R3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2lo2bs3LFB2FB3sp12L12p13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03x143SZC3APP3SGB2x23x153x163x174POSTS1R4STKn2LF3SIG4DALG2bs3LFB2D33ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3BUF3SIG2bs3LFB3DPB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB2D13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3BUF3SIG2bs3LFB3DSB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG4DALG2bs3LFB2D23ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB2D13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2lo2bs3LFB2FB3sp12L12p13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03x143SZC4APSG3SGB2x23x153x163x174POSTS1R4STKn2LF2PP3SIG2lo2bs3LFB2FB3sp12L12p13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03x143SZC4APSG3SGB2x23x153x163x174POSTS1R4STKn2LF2PP3SIG2lo2bs3LFB2FB3sp12L12p13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03x143SZC3APP3SGB2x23x153x163x174POSTS3END3BUF2bs2B32L12p13HL1S1P3BUF2B12p13Hp1FS2r13Hr13RNZFS1R2lo3LOS3ALOSS2L12p12p23Hq2S3SIG2lo4SGLOSFFS3END2L12p13HL1S2L12p13LR1S1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3SG02FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS3sp1S2PPS1R4STKn2sp2lo3SLO3sp13SP1FS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS2PP3SIG2D1FFFS3SIGS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS2r13Hr12E0S2r12X03NE0SFS1R3HIA4STKn1h2sp2lo3TOP2HTS3BUF3SIG2bs3DSBFS1P2p13Hp12p24Hp2aFS2loFSSSSFS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBFS3SIGFS1R4STKn4NAM02LF2sp2PP3SIG4DALG2lo2bs3LFB3PP04PPLO3SG03DA03SLO3SPH2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SPR2F04SP1R3SGBS1P3END2L12p13Hp13HL12p23Hq2FS3SIGFFFS2r13Hr1S1P3END2B2FFFFS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBFFS2r13Hr1S1R3BUF2lo2bs3LOS3ALO3BCES1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBFS3BUF2bs3B47FS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R2lo3LOSS3SIGFFFS3SIGFFS3SIG2r03ALS1q1r1H2H02q02H43sp14SP1MFFFS2sp3sp1SS2sp2lo3sp13SP1S1R4STKn4NAM02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFFFFFFFFFFFFFFFFFS1R4STKn2sp2lo3SLO3sp13SP1FFFFFFFS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG4DALG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG4DALG2lo2bs3LFB3SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO2F13SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG4DALG2lo2bs3LFB4DALO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG4DALG2lo2bs3LFB3SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO2F13SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3BUF3SIG4DALG2lo2bs3LFB3SLO3LOS3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO3BCE3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO2F13SGBS1R4STKn2LF2PP3SIG2lo2bs3LFB4PPLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO2F13SGBS1R4STKn2LF3SIG2lo2bs3LFB4SGLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG4DALG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG4DALG2lo2bs3LFB4DALO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3BUF3SIG2lo2bs3LFB3SLO3LOS3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO3BCE3SGBS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO3SGBFS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBFS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3PP03ALS3SG03DA02FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SPR2F04SP1R3SGBS1R4STKn2LF2sp3SIG4DALG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stFS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC4SP1R3SGB2HBS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBFFS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG4DALG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG4DALG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBFS1R4STKn2LF2sp3SIG4DALG2lo2bs3LFB3SLO3LOS3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO3SGB2HB5Ha_st5Hl_stFS1R4STKn2LF3SIG3slo2bs3LFB4SLOS3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG4DALG3slo2bs3LFB4SLOS3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGB2HB5Ha_stFS1R4STKn2LF2sp3SIG4DALG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stFS1R4STKn2LF2sp3SIG4DALG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG4DALG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stFFFS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3ALP3PP02FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SPR2F04SP1R3SGBFS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R3HIA4STKn1h2LF2sp3SIG4DALG3slo2bs3LFB3TOP3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC2HT3SGB2HB5Ha_st5Hl_stS1R3HIA4STKn1h2LF2sp3SIG3slo2bs3LFB3TOP3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC2HT3SGBFS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC4SP1R3SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC2F03SGB". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND FREE GETTAG STKn PHIn_mono FFRn_mono CNTn_mono GETSIG ALGNULL MCI GETNAME SERIAL GETINT NAM0 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALS SG0 CWS SGLO DSB ALD DA0 CRDA DALO Q1 Q2 Q3 D1 D2 D3 SLOS SLOL SLO TOP SPA SPH TPV LOS"] Lemma SEG2 : forall (FB sp1 : Z) (w0 w1 w2 L1 : word) (k0 k8 kE k16 k24 : word) (jA jB : list byte)
      (p1 : Z) (ver vpd stg spd : word) (sl0 sq0 : Z) (j48 : list byte) (mg : byte) (pad7 : list byte) (irt irp irl irq : word)
      (at0 apd0 aln0 aq0 bt0 bpd0 bln0 bq0 tg0 spad : word) (len0 q0 : Z) mc moc hc
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6v s8v : word),
    gvS FB sp1 X0 0 0 w0 w1 w2 L1 (Z_to_bv 8 0) k0 k8 kE k16 k24 jA jB p1
        ([C4 ver; C4 vpd] ++ buf_cells stg spd sl0 sq0 ++ name_blob j48 0 mg pad7 ++ [C4 irt; C4 irp; C8 irl; C8 irq] ++ [C4 at0; C4 apd0; C8 aln0; C8 aq0] ++ [C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0 ++ [C8 (Z_to_bv 64 0)])
        [] mc moc hc ->
    P + 2 <= p1 -> bv_unsigned L1 <= END - p1 ->
    havol asegs R HIA h + PHIsi NB <= AVOL_MAX -> hfr asegs R HIA h + FFRsi NB d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 FB) (Z_to_bv 64 SIG) (Z_to_bv 64 PP) (Z_to_bv 64 DALG) s6v (Z_to_bv 64 (FB + 32)) s8v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
                      (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x98fc0) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s8v. intros D Hp1 HL1 BUD BUDF UW. pose proof D as D0. gvS_open D. rt_facts. walk_prep.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as Dnn.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NAM0 STKn0 NRT; lia).
    pose proof (CNTn_mono 0 NB ltac:(clear - B1 B2; lia)) as CS0'. pose proof (PHIn_mono 0 NB ltac:(clear - B1 B2; lia)) as PS0. pose proof (FFRn_mono 0 NB (d + 1) ltac:(clear - B1 B2; lia)) as FS0.
    pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBUF) as OBUFc.
    pose proof (blocks_below_hm R HIA hc _ _ mc _ HHc ltac:(intros b Hb; exact Hb)) as BBc.
    destruct (BBc (BUF, n) ltac:(apply in_or_app; right; exact BIN)) as [_ BCE]. cbn [fst snd] in BCE.
    pose proof (rw_cells_bound _ _ _ _ CSG) as SGB. rewrite SZC in SGB.
    pose proof (bv_unsigned_in_range 64 L1) as LR1. unfold bv_modulus in LR1. cbn [Z.pow Z.of_N Pos.pow] in LR1.
    unfold buf_cells, name_blob in CSG. cbn [app] in CSG.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    do 15 zstep.
    do 6 zstep.
    match goal with |- context [Z_to_bv 64 (p1 + bv_unsigned L1)] => idtac | |- ?g => idtac "ES-FORM" end.
    (* [comment removed for export] *)
    chunk_split CSG 1%nat CVER CREST.
    lazymatch type of CREST with rw_cells _ _ ?a _ => replace a with (SIG + 4) in CREST by (clear; lia) end.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HH) as ABc end end.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with SSx : sshad _ _ mx ?slo' ?shi |- _ =>
      assert (OSTK : aobj asegs AL (hcs asegs R HIA hc) mx (sp1 - 48) 8) by
        (apply (aobj_of_sshad0 AL _ mx slo' shi (sp1 - 48) 0 CSOKc SSx);
         [ clear - SLO SLOL SP1 NS1 NAM0 STKn0 NRT; lia | clear - SP1; lia | clear - SP1M; Z.div_mod_to_equations; lia
         | clear - SP1 SLO SLOL LOS ALO ACP NS1 NAM0 STKn0 NRT; lia
         | eapply crange_sub; [exact SCSc| clear - SLO SP1 NS1 NAM0 STKn0 NRT; lia| clear - SP1; lia] ]) end end.
    pose proof GETINT as GI'. unfold asn1_get_int_stmtA, A_ASN1_GET_INT_G in GI'.
    lazymatch goal with OPx : aobj _ _ (hcs asegs R HIA hc) _ PP 8, OSx : aobj _ _ (hcs asegs R HIA hc) _ SIG 200, OBx : aobj _ _ (hcs asegs R HIA hc) _ BUF n |- _ =>
    acallxA_sp sp1
      (eapply GI' with (CS := hcs asegs R HIA hc) (PP := PP) (VALP := SIG) (P := p1) (END := p1 + bv_unsigned L1) (BUF := BUF) (bs := bs) (lo := lo) (valv := ver);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact CSOKc | exact ABc | exact OSTK | exact (art_alwf asegs R HIA) | exact OPx | exact OBx | exact B5 | exact ALP | exact PP0 | exact SG0 | exact CVER | reflexivity
               | lazymatch goal with
                 | |- rw_cells _ _ PP _ => eassumption
                 | |- bytes_at _ _ BUF bs => eassumption
                 | |- stk _ _ lo _ => assumption
                 | |- mem_inv _ _ => assumption
                 | |- BUF <= p1 => clear - Hp1 B1; lia
                 | |- p1 <= p1 + _ => clear - LR1; lia
                 | |- p1 + _ <= BUF + n => clear - HL1 B3; lia
                 | |- BUF + n < 2 ^ 63 => clear - B47; lia
                 | |- PP + 8 <= SIG \/ _ => clear - D1; lia
                 | |- n = 0 \/ PP + 8 <= BUF \/ _ => right; exact DPB
                 | |- n = 0 \/ SIG + 4 <= BUF \/ _ => clear - DSB; lia
                 | |- SIG mod 4 = 0 => clear - ALS; Z.div_mod_to_equations; lia
                 | |- lo <= sp1 - 64 => clear - SLO SP1 NS1 NAM0 STKn0 NRT; lia
                 | |- alloc_ceiling <= lo => clear - ALO LOS; lia
                 | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                 | |- crange _ lo _ => eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]
                 | |- PP + 8 <= lo \/ _ => left; exact PPLO
                 | |- SIG + 4 <= lo \/ _ => left; clear - SGLO; lia
                 | |- n = 0 \/ BUF + n <= lo \/ _ => right; left; clear - BCE ALO LOS; lia
                 | |- aobj _ _ _ _ SIG 4 => eapply aobj_sub; [exact OSx| clear; lia| clear; lia]
                 | |- _ = Z_to_bv 64 (p1 + bv_unsigned L1) => first [reflexivity | symmetry; apply bv_eq; rewrite ?Z_to_bv_unsigned; reflexivity | match goal with |- ?g => idtac "A1-FORM:" g end]
                 end
               | match goal with |- ?g => idtac "GI-PRE-LEFT:" g end ])
    end.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "GI-LEFT:" g end.
    clear GI' ABc OSTK.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r1 end.
    match goal with H : _ < r1 <= 0 |- _ => rename H into Hr1 end.
    match goal with H : r1 = 0 -> _ |- _ => rename H into HOK1 end.
    match goal with H : p1 <= ?pp <= p1 + _ |- _ => rename H into Hq2; rename pp into p2 end.
    lazymatch goal with H : rw_cells _ ?mx SIG [C4 ?vv] |- _ => rename vv into v2; rename H into CVER2; rename mx into m2 end.
    assert (Hp2E : P <= p2 <= END) by (clear - Hq2 Hp1 HL1; lia).
    (* [comment removed for export] *)
    lazymatch goal with CRx : rw_cells _ m2 (SIG + 4) ?rest |- _ =>
      assert (CSG2 : rw_cells asegs m2 SIG (C4 v2 :: rest)) by (change (rw_cells asegs m2 SIG ([C4 v2] ++ rest)); apply rw_cells_app; split; [exact CVER2| cbn [cells_size csize Nat.add]; exact CRx]);
      clear CRx
    | |- _ => idtac "SEG2: no CREST at m2" end.
    assert (G2 : gvS FB sp1 X0 0 0 w0 w1 w2 L1 (Z_to_bv 8 0) k0 k8 kE k16 (Z_to_bv 64 DALG) jA jB p2
              ([C4 v2; C4 vpd] ++ buf_cells stg spd sl0 sq0 ++ name_blob j48 0 mg pad7 ++ [C4 irt; C4 irp; C8 irl; C8 irq] ++ [C4 at0; C4 apd0; C8 aln0; C8 aq0] ++ [C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0 ++ [C8 (Z_to_bv 64 0)])
              [] m2 moc hc).
    { unfold buf_cells, name_blob. cbn [app]. gvA_fin HKc MFc (mo_frame_refl moc). }
    (* [comment removed for export] *)
    destruct (Z.eq_dec r1 0) as [R0|RNZ].
    - subst r1. pose proof (HOK1 eq_refl) as Hp2a. clear HOK1 Hr1.
      do 11 zstep.
    (* [comment removed for export] *)
      zstep. if_cases KB; zify_cond KB.
    { (* [comment removed for export] *)
      seg2_pc_is 0x99184. zstep. intros moq [HKq MFq].
      eapply (OUT R HIA) with (STKn := STKn) (PHIa := 0) (FFRa := 0) (slo := slo) (d := d) (lo := lo) (hc := hc) (mc := m2) (moc := moq) (ar := 0) (nodes := []) (inext := 0)
                              (pre := [C4 v2; C4 vpd] ++ buf_cells stg spd sl0 sq0) (j48 := j48) (mg := mg) (pad7 := pad7)
                              (post := [C4 irt; C4 irp; C8 irl; C8 irq] ++ [C4 at0; C4 apd0; C8 aln0; C8 aq0] ++ [C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0)
                              (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
        first [ sec_hyps | reflexivity | exact UW
              | lazymatch goal with
                | |- name_chain _ _ _ _ _ _ => cbn; reflexivity
                | |- List.NoDup [] => constructor
                | |- _ < 0 <= 0 => clear; lia
                | |- havol _ _ _ _ + _ + _ <= _ => cbn [length Z.of_nat]; unfold A_pkcs7_signer_C.PHIsi in BUD; unfold AVOL_CALL in *; clear - BUD PS0 CS0'; nia
                | |- hfr _ _ _ _ + _ + _ <= _ => cbn [length Z.of_nat]; unfold A_pkcs7_signer_C.FFRsi in BUDF; unfold fr_charge in *; clear - BUDF FS0 CS0' Dnn; nia
                | |- 0 + _ <= A_pkcs7_signer_C.PHIsi _ _ _ => cbn [length Z.of_nat]; unfold A_pkcs7_signer_C.PHIsi; unfold AVOL_CALL in *; clear - PS0 CS0'; nia
                | |- 0 + _ <= A_pkcs7_signer_C.FFRsi _ _ _ _ => cbn [length Z.of_nat]; unfold A_pkcs7_signer_C.FFRsi; unfold fr_charge in *; clear - FS0 CS0' Dnn; nia
                end
              | (lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signer_C.gvS] => idtac end end;
                 eapply A_pkcs7_signer_C.gvS_mo; [| exact HKq| exact MFq]; unfold A_pkcs7_signer_D.SC, name_blob, buf_cells in *; repeat rewrite <- app_assoc; cbn [app]; exact G2)
              | match goal with |- ?g => idtac "SEG2-OUT1-LEFT:" g end ]. }
      clear KB. seg2_pc_is 0x9905c.
    (* [comment removed for export] *)
      (* [comment removed for export] *)
      intros moq [HKq MFq].
      eapply (SEG3 R HIA) with (STKn := STKn) (hc := hc) (mc := m2) (moc := moq) (ES := p1 + bv_unsigned L1) (p := p2)
                               (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
        first [ sec_hyps | exact BUD | exact BUDF | exact UW
              | eapply A_pkcs7_signer_C.gvS_mo; [exact G2| exact HKq| exact MFq]
              | clear - Hp1 Hp2a Hq2 HL1; lia
              | match goal with |- ?g => idtac "SEG2-SEG3-LEFT:" g end ].
    - zstep. if_cases KV; zify_cond KV.
      { seg2_pc_is 0x99030. exfalso.
        first [ clear - KV RNZ Hr1; lia
              | revert KV; first [change 18446744073709551615 with (Z.ones 64) | idtac]; rewrite ?Z.land_ones by (clear; lia);
                rewrite ?(mod64_neg_small r1) by (clear - RNZ Hr1; lia); intros KV; clear - KV RNZ Hr1; lia ]. }
      do 4 zstep.
      change 18446744073709551615 with (Z.ones 64); rewrite (Z.land_ones r1 64) by (clear; lia).
      lazymatch goal with |- context [bv_swrap 32 (r1 mod 2 ^ 64 + ?K)] => rewrite (swrap32_errsum r1 K) by (clear - Hr1 RNZ; lia) end.
      zpre.
      do 11 zstep.
      zstep. if_cases KB; zify_cond KB.
      2: { seg2_pc_is 0x9905c. exfalso. apply KB.
           lazymatch goal with |- context [Z.land (r1 + ?c) ?M <? 1] =>
             replace (Z.land (r1 + c) M <? 1) with false;
             [ cbn [Z.b2z]; apply Z.land_0_r
             | symmetry; apply Z.ltb_ge; change M with (Z.ones 64); rewrite Z.land_ones by (clear; lia);
               rewrite (mod64_neg_small (r1 + c)) by (clear - Hr1; lia); clear - Hr1; lia ] end. }
      seg2_pc_is 0x99184. zstep. intros moq [HKq MFq].
        eapply (OUT R HIA) with (STKn := STKn) (PHIa := 0) (FFRa := 0) (slo := slo) (d := d) (lo := lo) (hc := hc) (mc := m2) (moc := moq) (ar := 0) (nodes := []) (inext := 0)
                              (pre := [C4 v2; C4 vpd] ++ buf_cells stg spd sl0 sq0) (j48 := j48) (mg := mg) (pad7 := pad7)
                              (post := [C4 irt; C4 irp; C8 irl; C8 irq] ++ [C4 at0; C4 apd0; C8 aln0; C8 aq0] ++ [C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0)
                              (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
        first [ sec_hyps | reflexivity | exact UW
              | lazymatch goal with
                | |- name_chain _ _ _ _ _ _ => cbn; reflexivity
                | |- List.NoDup [] => constructor
                | |- _ < 0 <= 0 => clear; lia
                | |- havol _ _ _ _ + _ + _ <= _ => cbn [length Z.of_nat]; unfold A_pkcs7_signer_C.PHIsi in BUD; unfold AVOL_CALL in *; clear - BUD PS0 CS0'; nia
                | |- hfr _ _ _ _ + _ + _ <= _ => cbn [length Z.of_nat]; unfold A_pkcs7_signer_C.FFRsi in BUDF; unfold fr_charge in *; clear - BUDF FS0 CS0' Dnn; nia
                | |- 0 + _ <= A_pkcs7_signer_C.PHIsi _ _ _ => cbn [length Z.of_nat]; unfold A_pkcs7_signer_C.PHIsi; unfold AVOL_CALL in *; clear - PS0 CS0'; nia
                | |- 0 + _ <= A_pkcs7_signer_C.FFRsi _ _ _ _ => cbn [length Z.of_nat]; unfold A_pkcs7_signer_C.FFRsi; unfold fr_charge in *; clear - FS0 CS0' Dnn; nia
                end
              | (lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signer_C.gvS] => idtac end end;
                 eapply A_pkcs7_signer_C.gvS_mo; [| exact HKq| exact MFq]; unfold A_pkcs7_signer_D.SC, name_blob, buf_cells in *; repeat rewrite <- app_assoc; cbn [app]; exact G2)
              | match goal with |- ?g => idtac "SEG2-OUT2-LEFT:" g end ].
      all: match goal with |- ?g => idtac "SEG2-END-LEFT:" g | _ => idtac end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02A0@C40858145355.256C60410007123.255D10636937134.256D16071854214.256D2457516971.256 D32458870384.256D46794843979.256D60109446735.256D65008160014.256D68221095944.256K14960815226.256K20981739667.254K29378133114.256K30993319891.256K48171199513.256K4855522682.256 K53642109465.256K65858155712.255L11431517604.19 L14956783596.2  L15479883060.4  L20977711877.2  L21654730866.2  L2621559066.1   L26892418956.1  L27111942217.1  L27666008530.2  L27832436220.231L27940405558.11 L28316294259.18 L28563793217.5  L29391009772.3  L30507144274.2  L30997223346.3  L35666023782.13 L38072332913.3  L38235734261.1  L38308634325.0  L39076636629.0  L39332637397.0  L40228640085.0  L40281191306.3  L41251426164.1  L42488948659.2  L42927756920.1  L43317676572.3  L43359552379.3  L47870616696.2  L48171524228.2  L4859948780.3   L49233373885.2  L49493397620.5  L4952274081.0   L5021251703.1   L50678314462.3  L52753581537.3  L53617080676.3  L53646818791.3  L57387013391.2  L58972524609.3  L59090792514.3  L59308586248.2  L59427880762.240L60098763854.6  L60812373952.13 L62275882349.3  L62560708162.2  L64179129035.1  L64630569949.3  L65110679799.3  L65862516566.2  L66151427842.16 L66298372189.2  L66572605252.10 L66812728480.3  L67070089790.2  L67653551064.2  L67922604617.0  L881835912.0    L9080220944.4   L9356559676.18  O11960516644.256O14568686558.253O14912726833.255O18988691132.255O20866770946.256O22525005962.255O25522832421.256O30010457231.255O31364011300.256O3493317847.254 O37559489567.256O3821773283.256 O424351700.254  O44938202843.254O45108703401.253O49701823576.255O50011839873.254O52099334849.256O55209884805.254O64474006218.255O66321155265.256O7474055973.256 P30511339222.255P38078079190.253P42484919333.255P47876372191.254P49230739482.255P50671478649.254P53607099331.253P59105944293.256P62260666314.254P62545491173.256P66292560634.255P66818508295.256P67064334489.255Q10592533181.256Q10598576460.231Q10636937134.256Q11133374175.256Q11657053839.256Q17027695041.256Q17681074618.256Q19561597574.231Q21767670690.256Q21845213585.256Q23219026840.256Q27573751300.256Q27942454161.256Q2803826605.256 Q29775981542.256Q32681607669.256Q33137450695.256Q40249520655.231Q42439168719.256Q46794843979.256Q48118064779.256Q56530976407.256Q59865603600.256Q61957894121.256Q64683942374.256Q6771375012.256 Q9356756743.233 Q9633850233.231 Q9644583048.256 00000400800g02=02>02m03\04R05A06]07j0920:>0:b0;F0<S0=60>>0?90?:0?I0?J0?K0?P0?T0?X0?`0@O0@i0A_0A`0Aa0Ab0Ac0B>0B?0BC0BD0BE0BF0BG0BP0BT0BU0BZ0Be0C00C10C20C30C40C>0C?0C@0CA0CK0CL0CM0CT0C`0Ca0Cg0Ch0D20DT0DU0DV0DW0D`0Dj0Dk0EN0EO0E`0Ea0Eb0Ej0Ek0El0F;0Fj0Fk0Fl0Fm0Fn0Fo0G00G10G20G30G40G50G60G70G80G90G:0G;0G<0GV0GW0GX0GY0HD0I=0In0Jg0K`0LH0M;0Mo0N]0OR0P60Q10Qd0R@0R\0S80ST0SU0T10Td0Uo0Vb0Vc0W?0W@0Wk0XH0Xl0Xm0YT0Z00ZR0Zn0[Y0[Z0[[0\O0]<0]=0]_0^>0^]S2PPS2FBS1R4STKn2LF2sp2PP3SIG4DALG2bs2sj3LFB2FB3sp13SZCS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs2sj3LFB3PP03SG03DA03SLO3LOS2FB3sp13SP13SZC3SPR2F04SP1RFS1R4STKn2LF2sp2PP3SIG4DALG2bs2sj3LFB2FB3sp13SZCS1R4STKn2LF2sp2PP3SIG4DALG2bs2sj3LFB2FB3sp13SZCS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs2sj3LFB3LOS2FB3sp13SZCS1R4STKn2LF2sp2PP3SIG4DALG2bs2sj3LFB2FB3sp13SZCS1R3HIA4STKn1h2LF2sp2PP3SIG4DALG2bs2sj3LFB3PP03SG03DA03TOP2FB3sp12h13HTc3SP13SZC3SPR2F04SP1RS1R4STKn2LF2PP1P3END4DALG2lo2bs2sj3LFB2FB3sp13x153SZC3APD2x33x163x173x184POSTS1R4STKn2LF2PP1P3END2lo2bs2sj3LFB2FB3sp13x153SZC3APP2x33x163x173x184POSTS1R4STKn2LF2PP1P3END3BUF2lo2bs2sj3LFB2FB3sp13x153SZC3APB2x33x163x173x184POSTS1R4STKn2LF2PP3BUF2bs2sj3LFB3DPB3SZCS1R4STKn2LF2PP4DALG2bs2sj3LFB2D23SZCS1R4STKn2LF2PP1P3END3SIG2lo2bs2sj3LFB2FB3sp13x153SZC4APSG2x33x163x173x184POSTS1R4STKn2LF2PP3SIG2bs2sj3LFB2D13SZCS1R4STKn2LF2PP1P3END2lo2bs2sj3LFB2FB3sp13x153SZC3APP2x33x163x173x184POSTS1R4STKn2sp3BUF2lo3slo2bs4SLOS4SLOL3SLO3LOS3sp13SP13ALO3BCEFS3BUF2bs2FB3APBFFS3sp1S2spS2PPS2r13Hr1S1R4STKn2LF2sp2PP3SIG4DALG2bs2sj3LFB2FB3sp13SZCS1R4STKn2sp2lo3SLO3sp13SP1S1R4STKn2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F1FFFFS1R3HIA4STKn1h2sp2lo3TOP2HTFS2loSSSSS1R3HIA1hS2FBFS3SIGS2PP2FB3APPS1P2p14Hp1aFFFFS1P3END2B2SFFS1P3END2B2FFS2FB2F0S3BUF2bs3B47FS1i2HiFS1R2lo3LOSS1R4STKn2sp2PP2lo4PPLO3SLO3sp13SP1FFFS1R3HIA1hS1P3END2B2FS2FB2r03F641q1r1H2H02q02H43sp14SP1MFS2r13Hr11r2KT1q1HFFS2sp3sp1SSS2sp2lo3sp13SP1S1R4STKn4NAM02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFFFFFFFFFFFFFFFFFFS1R4STKn2sp2lo3SLO3sp13SP1FFFS1R4STKn2LF2sp2PP2lo2bs2sj3LFB4PPLO3SLO3SZCS1R4STKn2LF2sp2lo2bs2sj3LFB3SLO3LOS2FB3sp13SP13SZC3ALO2F1S1R4STKn2LF2sp2lo2bs2sj3LFB3SLO3LOS2FB3SZC3ALO2F1S1R4STKn2LF2sp2lo2bs2sj3LFB3SLO3LOS2FB3sp13SP13SZC3ALO2F1S1R4STKn2LF2sp2lo2bs2sj3LFB3SLO3LOS2FB3sp13SP13SZC3ALO2F1S1R4STKn2LF2PP2lo2bs2sj3LFB4PPLO3sp13SZCS1R4STKn2LF2sp2PP2lo2bs2sj3LFB4PPLO3SLO3sp13SP13SZCS1R4STKn2LF2sp3SIG2lo2bs2sj3LFB4SGLO3SLO3sp13SP13SZCS1R4STKn2LF2lo2bs2sj3LFB3LOS2FB3sp13SZC3ALO2F1S1R4STKn2LF2sp4DALG2lo2bs2sj3LFB4DALO3SLO3sp13SP13SZCS1R4STKn2LF2sp2bs2sj3LFB3sp13SP13SZCS1R4STKn2LF2sp3BUF2lo2bs2sj3LFB3SLO3LOS3sp13SP13SZC3ALO3BCES1R4STKn2LF2sp2PP2lo2bs2sj3LFB4PPLO3SLO3sp13SP13SZCS1R4STKn2LF2bs2sj3LFB2FB3SZCS1R4STKn2LF2bs2sj3LFB2FB3SZCS1R4STKn2LF2PP2bs2sj3LFB3SZCS1R4STKn2LF2bs2sj3LFB2FB3SZCFS1R4STKn2LF2PP2bs2sj3LFB3SZCS1R4STKn2LF2sp2PP2lo2bs2sj3LFB4PPLO3SLO3sp13SP13SZCS1R4STKn2LF2sp2PP3SIG4DALG2bs2sj3LFB3PP03SG03DA02FB3sp13F643SZC3SPR2F04SP1RS1R4STKn2LF2sp2lo2bs2sj3LFB3SLO3LOS3sp13SP13SZC3ALOFS1R4STKn2LF2bs2sj3LFB2FB3SZCFS1R4STKn2LF2sp2lo2bs2sj3LFB3SLO3sp13SP13SZCS1R4STKn2LF2bs2sj3LFB3sp13SZCS1R4STKn2LF2sp2bs2sj3LFB3sp13SP13SZCFS1R4STKn2LF2sp2lo2bs2sj3LFB3sp13SP13SZCS1R4STKn2LF2bs2sj3LFB2FB3SZCS1R4STKn2LF3slo2bs2sj3LFB4SLOS3SZCS1R4STKn2LF2PP2bs2sj3LFB3SZCS1R4STKn2LF2sp2lo2bs2sj3LFB3SLO3LOS3SZC3ALOFFS1R4STKn2LF2sp3SIG2lo2bs2sj3LFB4SGLO3SLO3sp13SP13SZCS1R3HIA4STKn1h2LF2sp3slo2bs2sj3LFB3TOP3SZC2HTFS1R4STKn2LF2bs2sj3LFB3sp13SZC4SP1RS1R4STKn2LF2bs2sj3LFB2FB3SZC2F0S1R4STKn2LF2bs2sj3LFB2FB3SZC2F0". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND FREE GETTAG STKn PHIn_mono FFRn_mono CNTn_mono GETSIG ALGNULL MCI GETNAME SERIAL GETINT NAM0 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALS SG0 CWS SGLO DSB ALD DA0 CRDA DALO Q1 Q2 Q3 D1 D2 D3 SLOS SLOL SLO TOP SPA SPH TPV LOS"] Lemma from_S1P :
    havol asegs R HIA h + PHIsi NB <= AVOL_MAX -> hfr asegs R HIA h + FFRsi NB d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    forall ms, S1P ms -> aevtA asegs (KF asegs R HIA h mo0) POST ms.
  Proof.
    intros BUD BUDF UW ms HS1.
    ddestruct HS1 as (FB & sp1 & h1 & m1 & x1 & t0 & t1 & t2 & a0 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & w0 & w1 & w2 & k0 & k8 & kE & k16 & k24 & jA & jB
                    & Ems & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & G4 & FSH & SAVE & RSL & SThi & STlo & MI1
                    & PPc & CSG & DAc & BYc & OPP & OSG & ODA & OBUF & APP0 & APS0 & APD0 & APB0 & PRES0 & SS1).
    subst ms. intros moc [HK0c MF0c].
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as Dnn.
    pose proof (CNTn_mono 0 NB ltac:(clear - B1 B2; lia)) as CS0'. pose proof (PHIn_mono 0 NB ltac:(clear - B1 B2; lia)) as PS0. pose proof (FFRn_mono 0 NB (d + 1) ltac:(clear - B1 B2; lia)) as FS0.
    assert (NB0 : 0 <= NB) by (clear - B2; lia).
    (* [comment removed for export] *)
    pose proof CSG as CSGt. unfold signer_cells in CSGt. cbn [sj0 sj_merged sj1 sj2] in CSGt.
    apply (rw_cells_typed asegs m1 SIG [] 80 _ _ [4; 4; 4; 4; 8; 8; 48]%nat) in CSGt; [| reflexivity].
    cbn [tcells Nat.eqb app] in CSGt.
    lazymatch type of CSGt with rw_cells _ _ _ ?cs =>
      let l1 := eval cbv beta iota delta [firstn] in (firstn 10 cs) in
      let l2 := eval cbv beta iota delta [skipn] in (skipn 11 cs) in
      lazymatch eval cbv beta iota delta [nth_error] in (nth_error cs 10) with Some (CB 96 ?b96) =>
        change (rw_cells asegs m1 SIG (l1 ++ CB 96 b96 :: l2)) in CSGt;
        apply (rw_cells_typed asegs m1 SIG l1 96 b96 l2 [4; 4; 8; 8; 4; 4; 8; 8; 4; 4; 8; 8; 4; 4; 8; 8]%nat) in CSGt; [| reflexivity];
        cbn [tcells Nat.eqb app] in CSGt
      end end.
    lazymatch type of CSGt with rw_cells _ _ _ [C4 ?x1; C4 ?x2; C4 ?x3; C4 ?x4; C8 ?x5; C8 ?x6; CB 48 ?y48; C8 _; C1 ?mg0; CB 7 ?pd7; C4 ?i1; C4 ?i2; C8 ?i3; C8 ?i4;
                                          C4 ?u1; C4 ?u2; C8 ?u3; C8 ?u4; C4 ?v1; C4 ?v2; C8 ?v3; C8 ?v4; C4 ?c1; C4 ?c2; C8 ?c3; C8 ?c4; C8 _] =>
      assert (CSGf : rw_cells asegs m1 SIG ([C4 x1; C4 x2] ++ buf_cells x3 x4 (bv_unsigned x5) (bv_unsigned x6) ++ name_blob y48 0 mg0 pd7 ++ [C4 i1; C4 i2; C8 i3; C8 i4]
                                             ++ [C4 u1; C4 u2; C8 u3; C8 u4] ++ [C4 v1; C4 v2; C8 v3; C8 v4] ++ buf_cells c1 c2 (bv_unsigned c3) (bv_unsigned c4) ++ [C8 (Z_to_bv 64 0)]))
        by (unfold buf_cells, name_blob; cbn [app]; rewrite !Z_to_bv_bv_unsigned; exact CSGt);
      clear CSGt
    | rw_cells _ _ _ ?cs => idtac "RETYPE-FORM:" cs end.
    lazymatch type of CSGf with rw_cells _ _ _ ?fine =>
    assert (G1 : gvS FB sp1 X0 0 0 w0 w1 w2 (Z_to_bv 64 0) (Z_to_bv 8 0) k0 k8 kE k16 k24 jA jB P fine [] m1 moc h1)
    end.
    { pose proof (art_lo asegs R HIA) as ALO.
      destruct (frame_factsA R HIA CS h1 LB LF m1 FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS) as (CFB & _).
      split; [exact HH1|]. split; [apply (proj2 (HKI moc)); exact HK0c|]. split; [exact MF0c|].
      split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [intros x Hx; rewrite Ehcs; exact Hx|].
      split; [rewrite Evol; clear; lia|]. split; [rewrite Efr; clear; lia|].
      split.
      { ddestruct PRES0 as (P0 & C1' & C2' & C3'). split; [| split; [exact C1'| split; [exact C2'| exact C3']]].
        eapply presA_weaken; [exact P0| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact I]. }
      split; [exact SP1|]. split; [exact SP1M|]. split; [exact F64|]. split; [exact FRSH|]. split; [exact CFB|].
      split; [exact FHD|]. split; [exact G4|]. split; [exact FSH|]. split; [exact SAVE|]. split; [exact RSL|]. split; [exact SThi|]. split; [exact STlo|].
      split; [exact PPc|]. split; [clear - B2; lia|]. split; [exact CSGf|]. split; [reflexivity|]. split; [exact DAc|]. split; [exact BYc|].
      split; [exact OPP|]. split; [exact OSG|]. split; [exact ODA|]. split; [exact OBUF|]. split; [exact MI1| exact SS1]. }
    clear HH1 HKI FHD G4 FSH SAVE RSL SThi STlo MI1 PPc CSG CSGf DAc BYc OPP OSG ODA OBUF PRES0 SS1 SP1 SP1M F64 FRSH Ehtop Estk Eflag Evol Efr.
    pose proof G1 as D. gvA_open D. rt_facts. walk_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NAM0 STKn0 NRT; lia).
    pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBUF) as OBUFc.
    pose proof (blocks_below_hm R HIA h1 _ _ m1 _ HHc ltac:(intros b Hb; exact Hb)) as BB1.
    destruct (BB1 (BUF, n) ltac:(apply in_or_app; right; exact BIN)) as [_ BCE]. cbn [fst snd] in BCE.
    pose proof (F3 BUF n ltac:(apply in_or_app; left; exact BIN)) as APB.
    pose proof (frame_apart_obj0 R HIA LB LF lo DALG 24 FB 64 FRSH CRDA ltac:(clear; lia) ltac:(clear; lia) LOS) as APD.
    lazymatch type of HHc with HM _ _ _ _ ?LBh ?LFh _ =>
      assert (INHq : In (FB, 24) (LBh ++ fdata LFh)) by (apply in_or_app; right; cbn; left; reflexivity);
      assert (INDq : In (FB + 32, 64 - 40) (LBh ++ fdata LFh)) by (apply in_or_app; right; cbn; right; left; reflexivity)
    end.
    apply (aevtA_enter asegs (KF asegs R HIA h1 moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA h1) as LAWS. pose proof (KF_kinv asegs R HIA h1 moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ h1 _ _ mx |- _ => pose proof (hm_abase asegs R HIA h1 _ _ mx HH) as ABc end end.
    frame_aobj FSH (FB + 32) 1%nat as OL.
    pose proof GETTAG as GT'. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG_G in GT'.
    acallxA_sp sp1
      (eapply GT' with (CS := hcs asegs R HIA h1) (PP := PP) (LENP := FB + 32) (P := P) (END := END) (BUF := BUF) (bs := bs) (tag := 48) (lo := lo) (lenv := Z_to_bv 64 0);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact OL | exact CSOKc | exact ABc | exact (art_alwf asegs R HIA) | exact OPPc | exact OBUFc | exact B1 | exact B2 | exact B3 | exact B5 | exact ALP | exact PP0 | reflexivity
               | lazymatch goal with
                 | |- rw_cells _ _ PP _ => eassumption
                 | |- rw_cells _ _ (FB + 32) _ => eassumption
                 | |- bytes_at _ _ BUF bs => eassumption
                 | |- stk _ _ lo _ => assumption
                 | |- mem_inv _ _ => assumption
                 | |- BUF + n < 2 ^ 63 => clear - B47; lia
                 | |- PP + 8 <= FB + 32 \/ _ => clear - APP; lia
                 | |- n = 0 \/ PP + 8 <= BUF \/ _ => right; exact DPB
                 | |- n = 0 \/ FB + 32 + 8 <= BUF \/ _ => right; clear - APB; lia
                 | |- (FB + 32) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                 | |- 0 < FB + 32 => clear - F0; lia
                 | |- lo <= sp1 - 16 => clear - SLO SP1 NS1 NAM0 STKn0 NRT; lia
                 | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                 | |- crange _ lo _ => eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]
                 | |- PP + 8 <= sp1 - 16 \/ _ => left; clear - PPLO SLO SP1 NS1 NAM0 STKn0 NRT; lia
                 | |- FB + 32 + 8 <= sp1 - 16 \/ _ => left; clear - F1 ALO LOS SLO SP1 NS1 NAM0 STKn0 NRT; lia
                 | |- n = 0 \/ BUF + n <= sp1 - 16 \/ _ => right; left; clear - BCE ALO LOS SLO SP1 NS1 NAM0 STKn0 NRT; lia
                 end
               | match goal with |- ?g => idtac "GT0-PRE-LEFT:" g end ]).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "GT0-LEFT:" g end.
    clear GT' ABc OL.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r1 end.
    match goal with H : _ < r1 <= 0 |- _ => rename H into Hr1 end.
    match goal with H : r1 = 0 -> _ |- _ => rename H into HOK1 end.
    match goal with H : P <= ?pp <= END |- _ => rename H into Hp1; rename pp into p1 end.
    lazymatch goal with H : rw_cells _ ?mx (FB + 32) [C8 ?lw] |- _ => rename lw into Lw; rename H into GL1; rename mx into m2 end.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    lazymatch goal with CSx : rw_cells _ m2 SIG ?fine |- _ =>
      assert (G2 : gvS FB sp1 X0 0 0 w0 w1 w2 Lw (Z_to_bv 8 0) k0 k8 kE k16 k24 jA jB p1 fine [] m2 moc h1) by (gvA_fin HKc MFc (mo_frame_refl moc))
    end.
    (* [comment removed for export] *)
    zstep. if_cases KT; zify_cond KT.
    - (* [comment removed for export] *)
      assert (R10 : r1 = 0).
      { change 18446744073709551615 with (Z.ones 64) in KT. rewrite ?Z.land_ones in KT by (clear; lia). clear - KT Hr1. Z.div_mod_to_equations. lia. }
      subst r1. destruct (HOK1 eq_refl) as [Hp1a HLw].
      intros moq [HKq MFq].
      lazymatch type of G1 with A_pkcs7_signer_C.gvS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?fine _ _ _ _ =>
      lazymatch fine with [C4 ?x1; C4 ?x2] ++ buf_cells ?x3 ?x4 ?z5 ?z6 ++ name_blob ?y48 0 ?mg0 ?pd7 ++ [C4 ?i1; C4 ?i2; C8 ?i3; C8 ?i4] ++ [C4 ?u1; C4 ?u2; C8 ?u3; C8 ?u4] ++ [C4 ?v1; C4 ?v2; C8 ?v3; C8 ?v4] ++ buf_cells ?c1 ?c2 ?z7 ?z8 ++ _ =>
      eapply (SEG2 FB sp1) with (hc := h1) (mc := m2) (moc := moq) (p1 := p1) (L1 := Lw)
                                (ver := x1) (vpd := x2) (stg := x3) (spd := x4) (sl0 := z5) (sq0 := z6) (j48 := y48) (mg := mg0) (pad7 := pd7)
                                (irt := i1) (irp := i2) (irl := i3) (irq := i4) (at0 := u1) (apd0 := u2) (aln0 := u3) (aq0 := u4) (bt0 := v1) (bpd0 := v2) (bln0 := v3) (bq0 := v4)
                                (tg0 := c1) (spad := c2) (len0 := z7) (q0 := z8);
        first [ exact BUD | exact BUDF | exact UW
              | eapply A_pkcs7_signer_C.gvS_mo; [exact G2| exact HKq| exact MFq]
              | clear - Hp1a; lia | exact HLw
              | match goal with |- ?g => idtac "FS-SEG2-LEFT:" g end ]
      | _ => idtac "FS: fine-list shape" end
      | ?t => idtac "FS: G1 shape" end.
    - (* [comment removed for export] *)
      intros moq [HKq MFq].
      lazymatch type of G2 with context [rw_cells] => idtac | _ => idtac end.
      lazymatch type of G1 with A_pkcs7_signer_C.gvS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?fine _ _ _ _ =>
      lazymatch fine with [C4 ?x1; C4 ?x2] ++ buf_cells ?x3 ?x4 ?z5 ?z6 ++ name_blob ?y48 0 ?mg0 ?pd7 ++ [C4 ?i1; C4 ?i2; C8 ?i3; C8 ?i4] ++ [C4 ?u1; C4 ?u2; C8 ?u3; C8 ?u4] ++ [C4 ?v1; C4 ?v2; C8 ?v3; C8 ?v4] ++ buf_cells ?c1 ?c2 ?z7 ?z8 ++ _ =>
      eapply (OUTA R HIA) with (STKn := STKn) (PHIa := 0) (FFRa := 0) (slo := slo) (d := d) (lo := lo) (hc := h1) (mc := m2) (moc := moq) (ar := r1) (nodes := []) (inext := 0)
                               (pre := [C4 x1; C4 x2] ++ buf_cells x3 x4 z5 z6) (j48 := y48) (mg := mg0) (pad7 := pd7)
                               (post := [C4 i1; C4 i2; C8 i3; C8 i4] ++ [C4 u1; C4 u2; C8 u3; C8 u4] ++ [C4 v1; C4 v2; C8 v3; C8 v4] ++ buf_cells c1 c2 z7 z8)
                               (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
        first [ sec_hyps | reflexivity | exact UW
              | lazymatch goal with
                | |- name_chain _ _ _ _ _ _ => cbn; reflexivity
                | |- List.NoDup [] => constructor
                | |- _ < r1 <= 0 => clear - Hr1; lia
                | |- havol _ _ _ _ + _ + _ <= _ => cbn [length Z.of_nat]; unfold A_pkcs7_signer_C.PHIsi in BUD; unfold AVOL_CALL in *; clear - BUD PS0 CS0'; nia
                | |- hfr _ _ _ _ + _ + _ <= _ => cbn [length Z.of_nat]; unfold A_pkcs7_signer_C.FFRsi in BUDF; unfold fr_charge in *; clear - BUDF FS0 CS0' Dnn; nia
                | |- 0 + _ <= A_pkcs7_signer_C.PHIsi _ _ _ => cbn [length Z.of_nat]; unfold A_pkcs7_signer_C.PHIsi; unfold AVOL_CALL in *; clear - PS0 CS0'; nia
                | |- 0 + _ <= A_pkcs7_signer_C.FFRsi _ _ _ _ => cbn [length Z.of_nat]; unfold A_pkcs7_signer_C.FFRsi; unfold fr_charge in *; clear - FS0 CS0' Dnn; nia
                end
              | (lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signer_C.gvS] => idtac end end;
                 eapply A_pkcs7_signer_C.gvS_mo; [| exact HKq| exact MFq]; unfold A_pkcs7_signer_D.SC, name_blob, buf_cells in *; repeat rewrite <- app_assoc; cbn [app] in *; exact G2)
              | match goal with |- ?g => idtac "FS-OUTA-LEFT:" g end ]
      | _ => idtac "FS2: fine-list shape" end
      | ?t => idtac "FS2: G1 shape" end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG UARG SM0 NS1 DIMG HMND FREE GETTAG PHIn_mono FFRn_mono CNTn_mono GETSIG ALGNULL MCI GETNAME SERIAL GETINT NAM0"] Theorem A_pkcs7_signer_spec :
    pkcs7_signer_stmtA asegs R HIA (A_pkcs7_signer_C.PHIsi PHIn CNTn) (A_pkcs7_signer_C.FFRsi FFRn CNTn) (A_pkcs7_signer_C.CNTsi CNTn) STKsg A_PKCS7_SIGNER.
  Proof.
    intros h LB LF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo PP P END BUF SIG DALG lo slo d bs dtg dpad dlen dq sj.
    intros HH HK0 LFB HPP ALP PP0 OPP CWP PPLO HBY BIN B1 B2 B3 B47 B5 B30 DPB HSG ALS SG0 OSG CWS SGLO DSB HDA ALD DA0 ODA CRDA DALO Q1 Q2 Q3 D1 D2 D3
           ST SS SLOS SLOL SLO TOP SPA SPH MI TPV NDL BUD UW BUDF -> -> -> ->.
    pose proof (hm_aobj_block asegs R HIA h _ _ m BUF (Z.of_nat (length bs)) HH BIN) as OBUF.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ _ (conj HK0 (mo_frame_refl mo))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo).
    { eapply (A_pkcs7_signer_A.pro_walk R HIA) with (STKn := STKn) (lo := lo) (slo := slo) (bs := bs) (P := P) (END := END) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq) (sj := sj);
        first [ exact HH | exact HPP | exact HBY | exact HSG | exact HDA | exact CWP | exact CWS | exact CRDA | exact ST | exact SS | exact OPP | exact OSG | exact ODA | exact OBUF | exact SLO
              | eassumption | match goal with |- ?g => idtac "PW-LEFT:" g end ]. }
    intros ms1 HS1.
    eapply from_S1P with (bs := bs);
      first [ exact HPP | exact HBY | exact HSG | exact HDA | exact CWP | exact CWS | exact CRDA | exact SLO | exact BUD | exact UW | exact BUDF | exact HS1 | exact ST | exact SS
            | eassumption | match goal with |- ?g => idtac "TH-LEFT:" g end ].
  Qed.
End Walk.
