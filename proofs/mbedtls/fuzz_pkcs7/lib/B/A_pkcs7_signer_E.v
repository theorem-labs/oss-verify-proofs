(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_pkcs7_signer.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag
     A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt A_pkcs7_signer_A A_pkcs7_signer_B A_pkcs7_signer_C A_pkcs7_signer_D A_pkcs7_getsig_A
     A_pkcs7_signers_A A_pkcs7_signers_C A_pkcs7_signers_D A_pkcs7_signers_G.
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
  Hypothesis NAM0 : 0 <= arl_need_amem R.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55857805827.21000003S1R". (* [comment removed for export] *)
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
  Local Notation gvS := (A_pkcs7_signer_C.gvS R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP P END BUF SIG DALG lo slo bs dtg dpad dlen dq).
  Ltac gvA_open D :=
    destruct D as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & PRES & SP1 & SP1M & F64 & FRSH & CFB
                   & FHD & G4 & FSH & SAVE & RSL & STb & STlo & PPc & Hpc & CSG & SZC & DAc & BYc & OPP & OSG & ODA & OBUF & MIc & SSc).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L38885538412.800000BS1R4STKn2sp2lo3SLO". (* [comment removed for export] *)
  Let SLOq : lo <= bv_unsigned sp - A_pkcs7_signers_A.STKs R STKn.
  Proof. unfold A_pkcs7_signers_A.STKs. unfold STKsg in SLO. clear - SLO NS1 NAM0 STKn0. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac sec_hyps :=
    first [ exact IMG | exact UARG | exact SM0 | exact NS1 | exact DIMG | exact HMND | exact CALLOC | exact FREE | exact STKn0 | exact NAM0 | exact GETSIG
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

  Local Notation SC := A_pkcs7_signer_D.SC.
  (* [comment removed for export] *)
  #[using="Type"] Lemma aevtA_KF_iff : forall (hq hc : HST asegs R HIA) moc Q ms,
    (forall mo, HK asegs R HIA hq mo <-> HK asegs R HIA hc mo) -> aevtA asegs (KF asegs R HIA hq moc) Q ms -> aevtA asegs (KF asegs R HIA hc moc) Q ms.
  Proof. clear - HIA. intros hq hc moc Q ms HI H mo [HK MF]. apply H. split; [apply (proj2 (HI mo)); exact HK| exact MF]. Qed.
  #[using="Type"] Lemma SNAME_in : forall names x, In x names -> In (x, NAME_SIZE) (SNAME (rev names)).
  Proof. clear - HIA. intros names x Hx. unfold SNAME. apply (in_map (fun y => (y, NAME_SIZE))). apply (proj1 (in_rev _ _)). exact Hx. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00`0?L10596430123.1 L10837002389.2 L10886305300.5 L12654381620.1 L1540877545.3  L1822632595.7  L23615739305.3 L24128180555.1 L24284734534.24L24284734663.11L27111942217.1 L30997941952.5 L32197162500.3 L32454903270.1 L35666023782.13L38308634325.0 L38780784261.9 L39280637297.0 L39332637397.0 L40228640085.0 L42927756920.1 L45363093875.3 L48184106943.3 L48858767035.1 L49091086716.5 L50059436232.1 L50296064826.1 L52045659405.3 L52992257876.1 L53642095165.7 L5652854654.7  L5652854783.20 L57626607040.8 L60098763854.6 L61016596749.1 L6158852410.8  L6203936179.1  L66151427842.16L66265140939.1 L67725608524.6 L67922604617.0 L68268705984.8 L6899380056.1  L9356559676.18 L9473079220.11 L9631767084.2  L9642703854.5  L9873114841.13 00000400<00S00X00d01A01K01O02E02m03103@03M03Q03l03m04M04N04O04P04U04^04j04o05F05K05O05[05_06<06R07<07[07e07j08J08O08k08o09D09E09_09c0:R0:o0;60;I0;lS2FBS3BUF2bsS3SIG3pre3mid4post4SZC0S3BUFS2sp3sp13SP1S3SIG4DALG2D33off1k4OFF04OFFKS1R3HIA2hcS2FBS1R4STKn2sp3SIG2lo4SGLO3SLO3sp13off1k3SP14OFFK1a2kk2H1S3SIG2FB3off1k4OFF04OFFK4APSG1a2kk2H12H2S2PPS2PP3BUF2bs3DPBS3SIG3pre3midS2FBS1R3HIA4STKn1h2sp2lo3TOP2HTSS3BUF3SIG2bs3DSB3off1k4OFF04OFFKSSSS3SIGS2FB1c2HcS2PP4DALG2D2S3SIGS3SIG3pre3mid4post4SZC0S3sp1S2FBS2sp3sp13SP1S2FBS2PP3SIG2D13pre3mid4post4SZC0S2PP2FB3APP1a2kk2H12H2S1R4STKn2sp2PP2lo4PPLO3SLO3sp13SP11a2kk2H1S2PP3SIG3off1k4OFF04OFFK2xq3HX0S1R2lo3LOSS3SIGS3SIG3pre3mid4post3off1k3SZp3SZmS3sp1S3sp12r04SP1M1q1r1H2H02q02H4S2FBS3SIG2lo4SGLO1a2kk2H2SS1R3HIA1h2sp3TOP2hc3HSc2HTS2FBS1R4STKn4NAM02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS2PP3SIG2D13pre3mid4post4SZC0S2FB2F0S3SIG3pre3off1k3SZpS1R4STKn2sp2lo3slo4SLOL3SLO3sp13SP1". (* [comment removed for export] *)
  #[using="IMG STKn NAM0 CWP PPLO BIN DPB CWS SGLO DSB CRDA DALO D1 D2 D3 SLOS SLOL SLO TOP LOS"] Lemma gvS_pcall : forall (FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 kE k16 k24 : word) (jA jB : list byte)
      (p : Z) (sgc : list cell) (Lc : list blk) mc moc hc (pre mid post mid' : list cell) (off k : Z) (m' : mem) (h' : HST asegs R HIA) (p' : Z),
    gvS FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE k16 k24 jA jB p sgc Lc mc moc hc ->
    sgc = pre ++ mid ++ post -> Z.of_nat (cells_size pre) = off -> Z.of_nat (cells_size mid) = k -> cells_size mid' = cells_size mid -> 0 <= off -> off + k <= 200 ->
    (forall x, outside W x -> outside X0 x) ->
    HM asegs R HIA h' (Lc ++ LB) ((FB, 64) :: LF) m' -> hcs asegs R HIA h' = hcs asegs R HIA hc ->
    htop asegs R HIA h' = htop asegs R HIA hc -> hstkhi asegs R HIA h' = hstkhi asegs R HIA hc -> hflag asegs R HIA h' = hflag asegs R HIA hc ->
    havol asegs R HIA h' = havol asegs R HIA hc -> hfr asegs R HIA h' = hfr asegs R HIA hc ->
    (forall mo, HK asegs R HIA h' mo <-> HK asegs R HIA hc mo) ->
    presA asegs R (Lc ++ LB) ((FB, 64) :: LF) sp1 sp1 (hstkhi asegs R HIA hc) [(PP, PP + 8); (SIG + off, SIG + off + k)] mc m' ->
    mem_inv asegs m' -> stk asegs m' lo sp1 -> sshad asegs AL m' slo sp1 ->
    rw_cells asegs m' PP [C8 (Z_to_bv 64 p')] -> P <= p' <= END -> rw_cells asegs m' (SIG + off) mid' ->
    gvS FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE k16 k24 jA jB p' (pre ++ mid' ++ post) Lc m' moc h'.
  Proof.
    intros until p'. intros D Esgc SZp SZm SZm' OFF0 OFFK HWX HH' Ecs Etop Estk Eflag Evol Efr HKiff HP' MI' ST' SS' PPc' Hp' CM'.
    gvA_open D. rt_facts. walk_prep. subst sgc.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NAM0 STKn0 NRT; lia).
    pose proof (fresh_apart_grow R HIA hc Lc LB LF mc FB 64 FRSH HHc) as FRSH3.
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hc) hc (Lc ++ LB) LF mc FB 64 lo HHc eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (_ & INF & INH & IND & AP & _ & F8 & FBLO & _ & _).
    assert (SUBc : forall b, In b (LB ++ fdata LF) -> In b ((Lc ++ LB) ++ fdata ((FB, 64) :: LF))).
    { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb| right; apply (fdata_cons_sub b [] FB 64 LF); exact Hb]. }
    assert (CRo : forall a kk, a + kk <= lo -> client_range L (LB ++ fdata LF) lo a kk -> client_range L ((Lc ++ LB) ++ fdata ((FB, 64) :: LF)) sp1 a kk).
    { intros a kk Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0| exact SUBc]. }
    assert (CRS1 : forall a kk, SIG <= a -> a + kk <= SIG + 200 -> client_range L ((Lc ++ LB) ++ fdata ((FB, 64) :: LF)) sp1 a kk).
    { intros a kk H1 H2. apply CRo; [clear - H2 SGLO; lia|]. eapply client_range_inside; [exact CWS| intros b Hb; exact Hb| exact H1| exact H2]. }
    assert (CSHD : forall c, FB <= c < FB + 64 -> cshd R (Lc ++ LB) ((FB, 64) :: LF) sp1 (hstkhi asegs R HIA hc) c).
    { intros c Hc. right; right; left. exists (FB, 64). split; [left; reflexivity| cbn; exact Hc]. }
    assert (DJF : forall a kk, FB <= a -> a + kk <= FB + 64 -> disjoint_from [(PP, PP + 8); (SIG + off, SIG + off + k)] a kk).
    { intros a kk H1 H2. cbn. split; [clear - H1 H2 APP; lia|]. split; [clear - H1 H2 APSG OFF0 OFFK; lia| exact I]. }
    assert (DJs : forall a kk, sp1 <= a -> disjoint_from [(PP, PP + 8); (SIG + off, SIG + off + k)] a kk).
    { intros a kk H1. cbn. split; [clear - H1 PPLO LOS SLO SP1 NS1 NAM0 STKn0 NRT; lia|]. split; [clear - H1 SGLO OFF0 OFFK LOS SLO SP1 NS1 NAM0 STKn0 NRT; lia| exact I]. }
    (* [comment removed for export] *)
    ddestruct (rw_cells_split3 asegs mc SIG pre mid post CSG) as (CS1 & _ & CS3).
    pose proof SZC as SZC0. rewrite !cells_size_app in SZC0.
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m' _ _ HP') in CS1; [| apply CRS1; [clear; lia| clear - SZC0; lia] | cbn [disjoint_from]; split; [clear - D1 SZC0; lia| split; [clear - SZp; lia| exact I]] ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m' _ _ HP') in CS3; [| apply CRS1; [clear; lia| clear - SZC0; lia] | cbn [disjoint_from]; split; [clear - D1 SZC0 SZp SZm; lia| split; [clear - SZp SZm; lia| exact I]] ].
    assert (CSG' : rw_cells asegs m' SIG (pre ++ mid' ++ post)).
    { apply rw_cells_join3; [exact CS1| rewrite SZp; exact CM'| rewrite SZm'; exact CS3]. }
    (* [comment removed for export] *)
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA hc) (Lc ++ LB) ((FB, 64) :: LF) sp1 sp1 (hstkhi asegs R HIA hc) [(PP, PP + 8); (SIG + off, SIG + off + k)] mc m' FB _ CSOKc) in FSH;
      [| cbn [cells_size csize Nat.add]; exact CFBc | exact F8 | clear - F0; lia | exact HP' | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m' _ _ HP') in FHD; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INH| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m' _ _ HP') in G4; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m' _ _ HP') in SAVE; [| apply client_range_stack; clear - SP1; lia| apply DJs; clear - SP1; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m' _ _ HP') in RSL; [| apply client_range_stack; clear; lia| apply DJs; clear; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ mc m' _ _ HP') in STb; [| clear; lia| apply DJs; clear; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m' _ _ HP') in DAc; [| cbn [cells_size csize Nat.add length buf_cells]; apply CRo; [exact DALO| exact CRDA] | cbn [cells_size csize Nat.add length buf_cells disjoint_from]; split; [clear - D2; lia| split; [clear - D3 OFF0 OFFK; lia| exact I]] ].
    assert (BYc' : bytes_at asegs m' BUF bs).
    { eapply presA_bytes_at0; [exact HP'| exact BYc|]. destruct (Nat.eq_dec (length bs) 0) as [E|NE]; [left; exact E| right].
      split; [eapply client_range_block; [apply in_or_app; left; apply in_or_app; right; exact BIN| clear; lia| clear; lia]|].
      cbn [disjoint_from]. split; [clear - DPB NE; lia|]. split; [clear - DSB OFF0 OFFK NE; lia| exact I]. }
    destruct (sshad_split asegs AL mc slo sp1 (bv_unsigned sp) SSc ltac:(clear - SP1 SLO SLOL NS1 NAM0 STKn0 NRT; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [_ SShi].
    apply (presA_sshad asegs R _ _ _ _ _ _ mc m' _ _ HP') in SShi; [| clear; lia| clear - HT TOP HSc; lia].
    pose proof (sshad_merge asegs AL m' slo sp1 (bv_unsigned sp) SS' SShi ltac:(clear - SP1 SLOL SLO NS1 NAM0 STKn0 NRT; lia)) as SSm.
    assert (AOB : forall A kk, aobj asegs AL CS mc A kk -> (kk <= 0 \/ (client_range L ((Lc ++ LB) ++ fdata ((FB, 64) :: LF)) sp1 A kk /\ sp1 <= sp1)) -> aobj asegs AL CS m' A kk).
    { intros A kk HO HR. eapply presA_aobj0; [exact CSOK| exact HP'| exact HO| intros xq Hx; eapply hcs_below_top; exact (HCSc xq Hx)| exact HR]. }
    (* [comment removed for export] *)
    split; [exact HH'|]. split; [apply (proj2 (HKiff moc)); exact HKc|]. split; [exact MFc|].
    split; [rewrite Etop; exact HTc|]. split; [rewrite Estk; exact HSc|]. split; [rewrite Eflag; exact HFc|].
    split; [intros xq Hx; rewrite Ecs; exact (HCSc xq Hx)|].
    split; [rewrite Evol; exact HVc|]. split; [rewrite Efr; exact HFRc|].
    split.
    { ddestruct PRES as (P0 & C1' & C2' & C3'). split; [| split; [exact C1'| split; [exact C2'| exact C3']]].
      eapply presA_trans; [exact P0|]. rewrite <- HSc.
      eapply presA_weaken; [exact HP'| intros b Hb; apply in_or_app; right; exact Hb| intros b Hb; right; exact Hb
                           | clear - SP1; lia| clear - SP1; lia| clear; lia|].
      intros xq Hx. pose proof (HWX xq Hx) as HX0. cbn [outside] in HX0 |- *. clear - HX0 OFF0 OFFK. lia. }
    split; [exact SP1|]. split; [exact SP1M|]. split; [exact F64|]. split; [exact FRSH|]. split; [exact CFB|].
    split; [exact FHD|]. split; [exact G4|]. split; [exact FSH|]. split; [exact SAVE|]. split; [exact RSL|]. split; [exact STb|]. split; [exact ST'|].
    split; [exact PPc'|]. split; [exact Hp'|]. split; [exact CSG'|]. split; [rewrite !cells_size_app, SZm'; rewrite !cells_size_app in SZC; exact SZC|].
    split; [exact DAc|]. split; [exact BYc'|].
    split; [apply AOB; [exact OPP| right; split; [apply CRo; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| clear; lia]]|].
    split; [apply AOB; [exact OSG| right; split; [apply CRS1; clear; lia| clear; lia]]|].
    split; [apply AOB; [exact ODA| right; split; [apply CRo; [exact DALO| exact CRDA]| clear; lia]]|].
    split; [apply AOB; [exact OBUF| destruct (Z.eq_dec n 0) as [E0|NE]; [left; rewrite E0; clear; lia| right; split; [| clear; lia]]]|].
    { eapply client_range_block; [apply in_or_app; left; apply in_or_app; right; exact BIN| clear; lia| clear; lia]. }
    split; [exact MI'| exact SSm].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma gvS_sgc : forall FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE k16 k24 jA jB p sgc sgc' Lc mc moc hc,
    gvS FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE k16 k24 jA jB p sgc Lc mc moc hc ->
    (rw_cells asegs mc SIG sgc -> rw_cells asegs mc SIG sgc') -> cells_size sgc' = 200%nat ->
    gvS FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE k16 k24 jA jB p sgc' Lc mc moc hc.
  Proof.
    intros until hc. intros D HR SZ'. gvA_open D.
    split; [exact HHc|]. split; [exact HKc|]. split; [exact MFc|]. split; [exact HTc|]. split; [exact HSc|]. split; [exact HFc|]. split; [exact HCSc|].
    split; [exact HVc|]. split; [exact HFRc|]. split; [exact PRES|].
    repeat match goal with |- _ /\ _ => split end;
      first [ exact (HR CSG) | exact SZ' | assumption | exact (proj1 SP1) | exact (proj2 SP1) | exact (proj1 Hpc) | exact (proj2 Hpc) | match goal with |- ?g => idtac "GVASGC-LEFT:" g end ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00k0@L10837002389.2  L1107921941.273 L12654381620.1  L12933749194.12 L14431917872.12 L15756354262.7  L19980016842.7  L20763674639.10 L21362739857.3  L23392786842.0  L25584983585.6  L25965952530.11 L27111942217.1  L29010569984.272L31863022963.4  L34603895532.0  L3558087884.2   L35666023782.13 L35915868660.4  L36021046681.2  L36772629717.0  L3760832063.9   L38308634325.0  L38365014529.3  L38723088065.7  L39279659947.3  L39332637397.0  L40228640085.0  L41189156086.1  L41202929119.273L42927756920.1  L43459388226.1  L46740740395.7  L46881206458.8  L46885531809.3  L48932718241.0  L49037504437.11 L53850830487.6  L56380991837.10 L58972524609.3  L60098763854.6  L66151426447.10 L66151427842.16 L66556294966.11 L67737097252.2  L68036673570.3  L7419122673.273 L9356559676.18  L9873114841.13  Q10649498890.281Q10651751567.280Q13733105586.280Q17701933584.281Q27940753584.280Q35294532397.280Q45353764144.280Q53380958617.281Q60071281945.281Q61847600945.28100000803203703U04404B04Z04n05805905M05^05b05c06306406=06X06h07007107W07X07e08E08N08O08P08U0:C0:H0:M0:]0;90;:0;;0;U0;k0<D0<P0<Z0<j0=N0=h0=i0>40A60Ae0BH0Cg0EF0Fe0HD0J20K\0M;0M<0M=0O?S3BUF2bsS1R4STKn2LF2sp2PP1P3END3BUF3SIG4DALG2bs3LFB3PP02B12B32B53SG03DA02FB3sp11p3pre3j485inext2mg4pad76post724spad5nodes3SZ13SZ23Hp13ACV3SPR4SP1R3BCE3SGB2p22tg3len1q4SZ2'3Hpc3SZC2F03Hq13Hq23Hq3S3BUFS1R4STKn2sp2PP2lo4PPLO3SLO3SPRS1R4STKn2sp3SIG2lo4SGLO3SLO3SPRS1R2lo3LOS3ALOS1R3HIA1h2sp3TOP3sp13SP1S1P1p2ES3Hp12p24Hp2'S3SIG2xq1HSS1P3END3BUF2B11p3HpcS1p2ES2p24Hp2'2KES2PPFS2sp3SPH3sp13SP1SS3SIG3SG0S1R3HIA4STKn1h2sp2lo3TOP2HTS3BUF3SIG2bs3DSBS2LF3LFBSS4FFRn4CNTn1P3END1d4FFRa5nodes3FFR3DnnSS3SIG2lo4SGLOS4PHIn4CNTn1P3END4PHIa5nodes3PHIS2PP2xq1HSSS3SIGS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13pre3j485inext2mg4pad76post724spad5nodes3SZ13SZ23SGB2tg3len1q4SZ2'3SZCS3SIGS3SIGS1P1p2ES3Hp13Hp2S1P3END1p2ES3Hpc3HES2p24Hp2'FSS1R4STKn2sp2lo3SLO3sp13SP1S3END3BUF2bs2B32ES3HESS1R3BUF2lo2bs3LOS3ALO3BCES3BUF2bs3B47S1R2lo3LOSS1r2Hr2r02KR1q1HS3sp12r04SP1M1q1r1H2H02q02H43SIG3ALSS1R4STKn2sp2lo3SLO3sp13SP1FS2PP3SIG2D1S1R4STKn2LF2sp2PP1P3END3BUF3SIG4DALG2bs3LFB3PP02B12B32B53SG03DA02FB3sp11p3pre3j485inext2mg4pad76post724spad5nodes2ES3SZ13SZ23Hp13HES3ACV3SPR4SP1R3BCE3SGB2p22tg3len1q4Hp2'4SZ2'3SZC2F03Hq13Hq23Hq3S1R4STKn4NAM02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R4STKn2sp2lo3slo4SLOL3SLO3sp13SP1S1R4STKn2LF2PP3SIG2bs3LFB3pre3j485inext2mg4pad76post724spad5nodes3SZ13SZ23SGB2tg3len1q4SZ2'3SZCS1R4STKn2LF2PP3SIG2bs3LFB3pre3j485inext2mg4pad76post724spad5nodes3SZ13SZ23SGB2tg3len1q4SZ2'3SZCS1R4STKn2LF2PP3SIG2bs3LFB3pre3j485inext2mg4pad76post724spad5nodes3SZ13SZ23SGB2tg3len1q4SZ2'3SZCS1R4STKn2LF2PP3SIG2bs3LFB3pre3j485inext2mg4pad76post724spad5nodes3SZ13SZ23SGB2tg3len1q4SZ2'3SZCS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13pre3j485inext2mg4pad76post724spad5nodes3SZ13SZ23SGB2tg3len1q4SZ2'3SP13SZCS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13pre3j485inext2mg4pad76post724spad5nodes3SZ13SZ23SGB2tg3len1q4SZ2'3SP13SZCS1R4STKn2LF2PP3SIG2bs3LFB3pre3j485inext2mg4pad76post724spad5nodes3SZ13SZ23SGB2tg3len1q4SZ2'3SZCFFS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3ALP3PP02FB3sp13pre3j485inext2mg4pad76post724spad5nodes3SZ13SZ23SPR4SP1R3SGB2tg3len1q4SZ2'3SZC2F0". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND FREE STKn CNTn_mono GETSIG NAM0 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALS SG0 CWS SGLO DSB DA0 CRDA DALO D1 D2 D3 SLOS SLOL SLO TOP SPA SPH TPV LOS"] Lemma SEG5 : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 kE k24 : word) (jA jB : list byte)
      (p : Z) (pre : list cell) (j48 : list byte) (inext : Z) (mg : byte) (pad7 : list byte) (post72 : list cell) (tg0 spad : word) (len0 q0 : Z)
      (nodes : list Z) mc moc hc (ES : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s7v s8v : word),
    gvS FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) k24 jA jB p (SC pre j48 inext mg pad7 (post72 ++ buf_cells tg0 spad len0 q0)) (SNAME (rev nodes)) mc moc hc ->
    cells_size pre = 32%nat -> cells_size post72 = 72%nat ->
    name_chain asegs (fun _ => True) mc (SNAME (rev nodes) ++ LB) inext nodes -> List.NoDup nodes ->
    (forall x, In x nodes -> forall B k, In (B, k) LB -> x + NAME_SIZE <= B \/ B + k <= x) ->
    Z.of_nat (length nodes) <= CNTsi NB -> P + 2 <= p -> p <= ES -> ES <= END ->
    havol asegs R HIA h + PHIa + Z.of_nat (length nodes) * AVOL_CALL <= AVOL_MAX ->
    hfr asegs R HIA h + FFRa + Z.of_nat (length nodes) * fr_charge (d + 1) <= FR_MAX ->
    PHIa + Z.of_nat (length nodes) * AVOL_CALL <= PHIsi NB -> FFRa + Z.of_nat (length nodes) * fr_charge (d + 1) <= FFRsi NB d ->
    Z.of_nat (length nodes) <= CNTsi (ES - P) -> PHIa <= PHIsi (ES - P) -> FFRa <= FFRsi (ES - P) d ->     (* [comment removed for export] *)
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 FB) (Z_to_bv 64 SIG) (Z_to_bv 64 PP) (Z_to_bv 64 1) (Z_to_bv 64 ES) s7v s8v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
                      (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x9939c) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s8v. intros D SZ1 SZ2 HC HND HAP CNT Hp1 Hp2 HES BUD BUDF PHI FFR CNTE PHIE FFRE UW. pose proof D as D0. gvA_open D. rt_facts. walk_prep.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as Dnn.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NAM0 STKn0 NRT; lia).
    pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBUF) as OBUFc.
    pose proof (blocks_below_hm R HIA hc _ _ mc _ HHc ltac:(intros b Hb; exact Hb)) as BBc.
    destruct (BBc (BUF, n) ltac:(apply in_or_app; right; exact BIN)) as [_ BCE]. cbn [fst snd] in BCE.
    pose proof (rw_cells_bound _ _ _ _ CSG) as SGB. rewrite SZC in SGB.
    (* [comment removed for export] *)
    assert (Esgc : SC pre j48 inext mg pad7 (post72 ++ buf_cells tg0 spad len0 q0)
                   = (pre ++ [CB 48 j48; C8 (Z_to_bv 64 inext); C1 mg; CB 7 pad7] ++ post72) ++ buf_cells tg0 spad len0 q0 ++ [C8 (Z_to_bv 64 0)]).
    { unfold A_pkcs7_signer_D.SC. repeat rewrite <- app_assoc. reflexivity. }
    assert (SZP : Z.of_nat (cells_size (pre ++ [CB 48 j48; C8 (Z_to_bv 64 inext); C1 mg; CB 7 pad7] ++ post72)) = 168).
    { rewrite !cells_size_app, SZ1, SZ2. reflexivity. }
    pose proof CSG as CSG'. rewrite Esgc in CSG'.
    destruct (rw_cells_split3 asegs mc SIG _ _ _ CSG') as (_ & CSIG & _). clear CSG'. rewrite SZP in CSIG.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    destruct (sshad_split asegs AL mc slo sp1 (bv_unsigned sp) SSc ltac:(clear - SP1 SLO SLOL NS1 NAM0 STKn0 NRT; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSlo SShi].
    pose proof GETSIG as GS'. unfold pkcs7_getsig_stmtA, A_PKCS7_GETSIG in GS'.
    eapply (aevtA_cut_evtA_KF asegs R HIA hc moc).
    { eapply GS' with (h := hc) (LB := SNAME (rev nodes) ++ LB) (LF := (FB, 64) :: LF) (PP := PP) (SIGB := SIG + 168) (P := p) (END := ES) (BUF := BUF) (bs := bs) (lo := lo) (slo := slo)
                      (tg0 := tg0) (pad := spad) (len0 := len0) (q0 := q0);
        rewrite ?(unsigned_lit sp1) by exact SP1R; unfold PKCS7_GETSIG_STACK_A;
        first [ exact HHc | exact PPc | exact CSIG | exact BYc | exact STlo | exact SSlo | exact SLOS | exact SLOL | exact MIc | exact TPV | exact NS1 | exact B5 | exact ALP | exact DPB
              | exact OPPc | exact OBUFc | exact CWPc | reflexivity
              | lazymatch goal with
                | |- (length _ < 512)%nat => cbn [length]; unfold LFMAX_CRT in LFB; clear - LFB; lia
                | |- BUF <= p => clear - Hpc B1; lia
                | |- p <= ES => exact Hp2
                | |- ES <= BUF + n => clear - HES B3; lia
                | |- BUF + n < 2 ^ 63 => clear - B47; lia
                | |- PP + 8 <= SIG + 168 \/ _ => clear - D1; lia
                | |- n = 0 \/ SIG + 168 + 24 <= BUF \/ _ => clear - DSB; lia
                | |- (SIG + 168) mod 8 = 0 => clear - ALS; Z.div_mod_to_equations; lia
                | |- 0 < PP /\ _ => split; [exact PP0| clear - PPLO LOS SLO SPR; lia]
                | |- 0 < SIG + 168 /\ _ => split; [clear - SG0; lia| clear - SGLO LOS SLO SPR; lia]
                | |- lo <= sp1 - 4208 => unfold STKsg in SLO; clear - SLO SP1 NS1 NAM0 STKn0 NRT; lia
                | |- lo <= sp1 - 112 - arl_need_smalloc R => unfold STKsg in SLO; clear - SLO SP1 NS1 NAM0 STKn0 NRT; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                | |- sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
                | |- PP + 8 <= lo \/ _ => left; exact PPLO
                | |- SIG + 168 + 24 <= lo \/ _ => left; clear - SGLO; lia
                | |- n = 0 \/ BUF + n <= lo \/ _ => right; left; clear - BCE ALO LOS; lia
                | |- client_range _ _ _ PP _ => exact (client_range_of_w L _ _ _ _ _ CWPc)
                | |- client_range _ _ _ (SIG + 168) _ => eapply client_range_inside; [exact CWSc| intros b Hb; exact Hb| clear; lia| clear; lia]
                | |- n = 0 \/ PP + 8 <= BUF \/ _ => right; exact DPB
                | |- client_range _ _ _ BUF _ => eapply client_range_block; [apply in_or_app; left; apply in_or_app; right; exact BIN| clear; lia| clear; lia]
                | |- client_wrange _ _ _ _ (SIG + 168) _ => eapply client_wrange_inside; [exact CWSc| intros b Hb; exact Hb| clear; lia| clear; lia]
                | |- aobj _ _ _ _ (SIG + 168) _ => eapply aobj_sub; [exact OSGc| clear; lia| clear; lia]
                end
              | match goal with |- ?g => idtac "GSIG-PRE-LEFT:" g end ]. }
    cbv beta. intros ms2 PO.
    ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & h2 & r & p2 & tg & len & q
                    & -> & HH2 & Ecs & Etop & Estk & Eflag & Evol & Efr & HKiff & HP2 & MI2 & ST2 & SS2 & Ea0 & Hr & PPc2 & CSIG2 & Hp2' & HOK).
    subst ua0. clear GS'.
    replace (ret_pc (Z_to_bv 64 0x993ac)) with (Z_to_bv 64 0x993ac : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in HP2, ST2, SS2 by exact SP1R.
    assert (G2 : gvS FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) k24 jA jB p2
                     ((pre ++ [CB 48 j48; C8 (Z_to_bv 64 inext); C1 mg; CB 7 pad7] ++ post72) ++ buf_cells tg spad len q ++ [C8 (Z_to_bv 64 0)]) (SNAME (rev nodes)) m2 moc h2).
    { eapply (gvS_pcall FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE _ k24 jA jB p _ (SNAME (rev nodes)) mc moc hc _ (buf_cells tg0 spad len0 q0) [C8 (Z_to_bv 64 0)] (buf_cells tg spad len q) 168 24 m2 h2 p2);
        first [ exact HH2 | exact Ecs | exact Etop | exact Estk | exact Eflag | exact Evol | exact Efr | exact HKiff | exact HP2 | exact MI2 | exact ST2 | exact SS2 | exact PPc2 | exact CSIG2 | exact SZP
              | eapply gvS_sgc; [exact D0| intros CX; rewrite Esgc in CX; exact CX| rewrite <- Esgc; apply SC_size; [exact SZ1| rewrite cells_size_app, SZ2; reflexivity]]
              | reflexivity | clear; lia | intros xq Hx; exact Hx
              | clear - Hp2' Hpc HES; lia
              | match goal with |- ?g => idtac "PCALL-LEFT:" g end ]. }
    assert (Esgc2 : (pre ++ [CB 48 j48; C8 (Z_to_bv 64 inext); C1 mg; CB 7 pad7] ++ post72) ++ buf_cells tg spad len q ++ [C8 (Z_to_bv 64 0)]
                    = SC pre j48 inext mg pad7 (post72 ++ buf_cells tg spad len q)).
    { unfold A_pkcs7_signer_D.SC. repeat rewrite <- app_assoc. reflexivity. }
    rewrite Esgc2 in G2.
    assert (SZ2' : cells_size (post72 ++ buf_cells tg spad len q) = 96%nat) by (rewrite cells_size_app, SZ2; reflexivity).
    (* [comment removed for export] *)
    assert (HC2 : name_chain asegs (fun _ => True) m2 (SNAME (rev nodes) ++ LB) inext nodes).
    { eapply (chain_presx asegs L _ _ _ mc m2 _ _ sp1 [(PP, PP + 8); (SIG + 168, SIG + 168 + 24)]);
        [ exact HC | intros xq Hx; eapply (chain_nodes_in asegs); [exact HC| exact Hx]
        | eapply heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP2)| intros b Hb; apply in_or_app; left; exact Hb| apply Z.le_refl| intros xq Hx; exact Hx]
        | unfold NAME_SIZE; clear; lia |].
      intros xq Hx. assert (HxL : In (xq, NAME_SIZE) (SNAME (rev nodes))) by (apply SNAME_in; exact Hx).
      cbn [disjoint_from]. split; [| split; [| exact I]].
      - pose proof (obj_apart_new R HIA hc (SNAME (rev nodes)) LB LF ((FB, 64) :: LF) mc lo (htop asegs R HIA h) PP 8 xq NAME_SIZE DIMG HHc ltac:(intros fb Hfb; right; exact Hfb) CWP ltac:(clear - ALO LOS; lia) ltac:(clear; lia) HxL ltac:(unfold NAME_SIZE; clear; lia)).
        clear - H. lia.
      - pose proof (obj_apart_new R HIA hc (SNAME (rev nodes)) LB LF ((FB, 64) :: LF) mc lo (htop asegs R HIA h) SIG 200 xq NAME_SIZE DIMG HHc ltac:(intros fb Hfb; right; exact Hfb) CWS ltac:(clear - ALO LOS; lia) ltac:(clear; lia) HxL ltac:(unfold NAME_SIZE; clear; lia)).
        clear - H. lia. }
    clear HHc HKc MFc HTc HSc HFc HCSc HVc HFRc PRES SP1 SP1M F64 FRSH CFB FHD G4 FSH SAVE RSL STb STlo PPc Hpc CSG SZC DAc BYc OPP OSG ODA OBUF MIc SSc D0 HC CSIG SSlo SShi OBUFc HP2 MI2 ST2 SS2 PPc2 CSIG2.
    clear CSOKc HT CFBc SCS03c SCS SCSc OPPc OSGc ODAc CRP CRS CRDg APP APSG F0 F1 F2 F3 STKH WL WCS WCP CWSc CWPc LAWS KINV.
    apply (aevtA_KF_iff h2 hc moc _ _ HKiff).
    pose proof G2 as D. gvA_open D. walk_prep.
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 moc) as KINV.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    { (* [comment removed for export] *)
      zstep.
      intros moq [HKq MFq].
      eapply (OUT R HIA) with (STKn := STKn) (PHIa := PHIa) (FFRa := FFRa) (slo := slo) (d := d) (lo := lo) (hc := h2) (mc := m2) (moc := moq) (ar := 0) (nodes := nodes)
                              (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
        first [ sec_hyps | exact SZ1 | exact SZ2' | exact HC2 | exact HND | exact BUD | exact BUDF | exact PHI | exact FFR | exact UW
              | eapply A_pkcs7_signer_C.gvS_mo; [exact G2| exact HKq| exact MFq]
              | clear; lia
              | match goal with |- ?g => idtac "SEG5-OUT1-LEFT:" g end ]. }
    assert (R0 : r = 0).
    { first [change 18446744073709551615 with (Z.ones 64) in KR; rewrite ?Z.land_ones in KR by (clear; lia) | idtac]. clear - KR Hr. Z.div_mod_to_equations. lia. }
    subst r. ddestruct (HOK eq_refl) as (Etg & Hq1 & Hq2 & Hq3). clear HOK KR Hr.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases KE; zify_cond KE;
      first [change 18446744073709551615 with (Z.ones 64) in KE; rewrite !Z.land_ones in KE by (clear - Hp2' Hpc HES Hp1 B1 B2 B3 B47 B5; lia) | idtac];
      rewrite ?Z.mod_small in KE by (clear - Hp2' Hpc HES Hp1 B1 B2 B3 B47 B5; lia).
    { (* [comment removed for export] *)
      intros moq [HKq MFq].
      eapply (OUT R HIA) with (STKn := STKn) (PHIa := PHIa) (FFRa := FFRa) (slo := slo) (d := d) (lo := lo) (hc := h2) (mc := m2) (moc := moq) (ar := 0) (nodes := nodes)
                              (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
        first [ sec_hyps | exact SZ1 | exact SZ2' | exact HC2 | exact HND | exact BUD | exact BUDF | exact PHI | exact FFR | exact UW
              | eapply A_pkcs7_signer_C.gvS_mo; [exact G2| exact HKq| exact MFq]
              | clear; lia
              | match goal with |- ?g => idtac "SEG5-OUT2-LEFT:" g end ]. }
    (* [comment removed for export] *)
    zstep.
    intros moq [HKq MFq].
    eapply (ret_walkS R HIA) with (STKn := STKn) (nodes := nodes) (inext := inext) (PHIa := PHIa) (FFRa := FFRa) (slo := slo) (d := d) (lo := lo) (hc := h2) (mc := m2) (moc := moq) (W := X0) (p := p2)
                                 (sj' := SGJ (cells_bytes pre ++ j48) mg pad7 (cells_bytes (post72 ++ buf_cells tg spad len q)))
                                 (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
      first [ sec_hyps | exact HC2 | exact HND | exact HAP | exact CNT
            | lazymatch goal with
              | |- PHIa <= _ => unfold AVOL_CALL in PHI; clear - PHI; lia
              | |- FFRa <= _ => unfold fr_charge in FFR; clear - FFR Dnn; lia
              | |- forall x, outside _ x -> outside _ x => intros xq Hxq; exact Hxq
              | |- _ < 0 <= 0 => clear; lia
              | |- 0 = 0 -> _ /\ _ => intros _; replace p2 with ES by (clear - KE Hp1 Hp2 Hp2' Hpc HES; lia); split; [exact PHIE| split; [exact FFRE| split; [exact CNTE| clear - Hp1 Hp2 HES; lia]]]
              | |- 0 = 0 -> _ => intros _; clear - KE Hp1 Hp2 Hp2' Hpc; lia
              | |- 0 <> 0 -> _ => intros X; exfalso; apply X; reflexivity
              end
            | (lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signer_C.gvS] => idtac end end;
               eapply gvS_sgc; [eapply A_pkcs7_signer_C.gvS_mo; [exact G2| exact HKq| exact MFq] | intros CX; eapply SC_signerA; [exact CX| exact SZ1| exact SZ2'] | reflexivity])
            | match goal with |- ?g => idtac "SEG5-RET-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
