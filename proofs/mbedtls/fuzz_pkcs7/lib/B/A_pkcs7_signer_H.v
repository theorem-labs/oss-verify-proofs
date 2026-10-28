(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_pkcs7_signer.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag
     A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt A_pkcs7_signer_A A_pkcs7_signer_B A_pkcs7_signer_C A_pkcs7_signer_D A_pkcs7_signer_E A_pkcs7_signer_F A_pkcs7_signer_G
     A_pkcs7_getsig_A A_asn1_get_alg_null_A A_x509_get_name_stmt A_x509_get_serial A_pkcs7_signers_A A_pkcs7_signers_C A_pkcs7_signers_D A_pkcs7_signers_G.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
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
  Hypothesis NAM0 : 0 <= arl_need_amem R.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55857805827.26000003S1R". (* [comment removed for export] *)
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
    first [ exact IMG | exact UARG | exact SM0 | exact NS1 | exact DIMG | exact HMND | exact CALLOC | exact FREE | exact STKn0 | exact NAM0 | exact GETSIG | exact ALGNULL | exact MCI | exact NBC | exact GETNAME | exact SERIAL
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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "09h0@C40858145355.283C40858145355.376C40860242543.303C60407910007.304C60410007123.282C9043944505.377 D10636937134.283D10636937134.377D10639034250.304D12949562016.282D12949562016.350D16069757090.304D16071854214.283D16899842714.304D16901939902.283D2455419791.304 D2457516971.283 D24582091142.377D25662884252.282D25662884252.350D31021624750.377D32456773204.304D32458870384.283D3953997537.260 D3953997537.282 D3953997537.303 D46792746863.304D46794843979.283D46794843979.377D59952099962.377D60109196847.282D60109196847.350D60109446735.283D60109446735.377D60111543915.304D60189065437.260D60189065437.282D60189065437.303D60498678367.377D65008160014.283D65010257194.304K10107971539.377K12838370724.282K12838370724.350K14958718046.302K14960815226.283K16603414433.377K18972226539.375K20981739667.281K20981739667.375K20983836855.302K25103330835.376K28788825731.282K28788825731.350K29378133114.283K29380230238.304K30993319891.283K30993319891.377K30995417079.304K31006132769.377K44164039966.282K44164039966.350K48169102397.302K48171199513.283K48171199513.376K4853425502.304 K4855522682.283 K49341710523.282K49341710523.350K49936266399.282K49936266399.350K53642109465.283K53642109465.376K53644206653.304K56577295428.375K65856058596.304K65858155712.282K65858155712.375L10111940530.3  L10115146064.10 L10470257411.336L10832924137.3  L10914754091.11 L1110002080.214 L1110426910.289 L11328261824.9  L11431517604.19 L12126572370.2  L12790317110.2  L12792389685.27 L12850865746.2  L13245553422.1  L1386317190.291 L14503517140.8  L14636542328.2  L14956783596.2  L15479883060.4  L15756354262.7  L1580389881.268 L16597070012.2  L16720171459.361L16722252919.193L16722252919.268L16855922378.289L16856283764.214L1685717371.0   L17661408117.214L1824911038.1   L18315423448.2  L18959349885.2  L19404986422.11 L2036051503.2   L20545738554.3  L20546686880.3  L20977711877.2  L21654730866.2  L22789151221.214L2337172835.214 L23700999155.193L23701062899.3  L23852584316.193L24109381028.8  L24789588439.14 L25103131278.2  L25584983585.6  L2621559066.1   L26974892722.2  L27111942217.1  L27666008530.2  L27832436220.258L27832436220.279L27940405558.11 L28316294259.18 L28632618922.2  L28776318325.2  L29391009772.3  L29745045590.364L2975252766.214 L29872045605.7  L29925996224.1  L29936708385.0  L30507144274.2  L30874558349.1  L30997223346.3  L31020860732.2  L31204426565.3  L31436896705.14 L31471780431.10 L32100533906.10 L32280122272.2  L33140404870.7  L33377192116.2  L34603895532.0  L35455319922.2  L35666023782.13 L35851064097.0  L35915868660.4  L36210178594.3  L3638965249.3   L36650016793.10 L37200085209.1  L37232046390.2  L38235734261.1  L38259954321.2  L38308634325.0  L385342792.1    L38756097386.193L39076636629.0  L39179469954.1  L39277835792.3  L39332637397.0  L40228640085.0  L40596013857.0  L41202929119.269L41202929119.290L41202929119.337L41202929119.361L41251426164.1  L42488948659.2  L42492001294.10 L42652040633.336L42742479599.8  L42927756920.1  L43317676572.3  L43873480711.2  L44061217931.2  L44166924249.3  L44167885381.336L44168742175.3  L44931842239.12 L45186664561.3  L46106660189.2  L46502749028.3  L46887489569.12 L46956377698.11 L47079827524.3  L47870616696.2  L47924454210.2  L48171524228.2  L4859172830.27  L4859948780.2   L49233373885.2  L49326776262.2  L49493397620.5  L49936279650.2  L5021251703.1   L50678314462.3  L50790731766.13 L51095541872.3  L53516896046.289L53517061009.268L53646839997.27 L53648387332.2  L53850830487.6  L55183406928.193L56380991837.10 L56581197778.2  L56847218714.1  L57387013391.2  L576250137.269  L576250137.290  L57698627611.2  L58230853255.13 L58972524609.3  L59036657398.1  L59090792514.2  L59092848705.27 L59308586248.2  L59427880762.270L60024037698.2  L60098763854.6  L6031628760.2   L60425790361.8  L60513344834.1  L60812373952.13 L61402546351.2  L61561077085.336L61567447837.193L61567447837.268L62275882349.3  L62560708162.2  L62586290822.10 L64179129035.1  L64283331834.16 L65042672357.361L65110679799.3  L65703474114.6  L65809642273.0  L65862516566.2  L66064443456.1  L66151427842.16 L66298372189.2  L66572605252.10 L66812728480.3  L67070089790.2  L67742368660.8  L7077560012.2   L881835912.0    L9080220944.4   L923304978.2    L9356559676.18  O11135157987.377O11958419456.302O11960516644.283O14664926154.375O14912726833.283O14912726833.375O14914823957.304O18988691132.282O18988691132.375O18990788248.302O20866770946.283O20868868134.304O22525005962.282O22525005962.375O22527103150.304O2474378910.375 O25522832421.283O25524929537.302O27557489321.280O27557489321.374O27559586445.301O30010457231.282O30012554411.302O30870739931.375O31361914112.304O31364011300.283O31855893893.375O3337348299.377 O33655933768.375O34144639763.376O34167073427.374O3491220723.302 O3493317847.281 O3493317847.375 O37557392443.304O37559489567.283O37559489567.377O3821773283.283 O3823870407.304 O40786154527.377O41270762881.375O424351700.281  O426448880.302  O43237831243.377O44938202843.281O44940300031.302O4521547224.375 O48274524197.376O49699726460.304O49701823576.283O50009742757.302O50011839873.281O50011839873.375O51462488883.375O52099334849.283O52099334849.376O52101432037.304O52449749665.377O55209884805.281O55211981985.302O56006291749.376O60532504563.375O64471909102.302O64474006218.282O66321155265.283O66321155265.376O66323252453.302O7471958785.304 O7474055973.283 O7902534110.280 O7904631290.301 P12115299733.260P12115299733.282P12115299733.303P12795822833.260P12795822833.282P12795822833.303P14639119327.375P2042605906.282 P2042605906.350 P20539858183.377P26964975637.377P28627113325.260P28627113325.282P28627113325.303P30511339222.282P30511339222.375P30513436402.302P32294539623.282P32294539623.350P33378753043.375P37243319281.260P37243319281.282P37243319281.303P38261788758.260P38261788758.282P38261788758.303P42484919333.282P42487016449.302P44067980844.375P44164039966.260P44164039966.282P44164039966.303P45191338738.301P45193435862.280P46116577274.375P46490677735.301P46492774851.280P46492774851.374P47089842915.375P47874275067.302P47876372191.281P47922934245.376P49228642366.304P49230739482.283P50671478649.281P50671478649.375P50673575773.302P51092966103.374P57713046236.260P57713046236.282P57713046236.303P59103847105.304P59105944293.283P60018324453.376P61387853746.375P62260666314.281P62262763502.302P62545491173.283P62547588289.302P66292560634.282P66294657758.302P66816411171.304P66818508295.283P67064334489.283P67064334489.375P67066431677.304Q10592533181.283Q10594630297.304Q10598576460.258Q10598576460.279Q10598692378.278Q10598857381.299Q10636937134.283Q10636937134.377Q10636952905.346Q10637070221.370Q10639034250.304Q10649498890.279Q10649498890.300Q10649498890.347Q10649498890.371Q10651584438.299Q10651749129.278Q11133374175.283Q11135471355.304Q11657053839.283Q11659151019.304Q12135079354.377Q126041979.347  Q12656864878.279Q12656864878.347Q12949562016.282Q12949562016.350Q12951513248.281Q12951513248.349Q13442034895.279Q13442034895.347Q13730668148.346Q13731009712.370Q13732682891.299Q13733105716.278Q1430820523.278 Q1431181844.299 Q1437095822.256 Q15234287761.278Q15249047727.370Q15249295979.346Q15889245814.346Q15904106550.278Q17025597925.304Q17027695041.283Q17027695041.377Q17402714361.346Q17681074618.283Q17683171742.304Q17701933584.279Q17701933584.300Q17701933584.347Q17701933584.371Q18634908500.377Q19398679185.377Q19561597574.258Q19561597574.279Q21157640433.280Q21157640433.348Q21765573510.304Q21767670690.283Q21845213585.283Q21847310773.304Q21915212471.299Q21925221622.346Q23216929724.304Q23219026840.283Q23258654747.282Q23258654747.350Q25660900252.281Q25660900252.349Q25662884252.282Q25662884252.350Q25825615593.377Q27458512306.260Q27458512306.282Q27458512306.303Q27573751300.283Q27575848480.304Q27942454161.283Q27944551349.304Q2803826605.283 Q2805923721.304 Q28465177121.257Q28465177121.279Q28465177121.300Q29065305745.377Q29775981542.283Q29778078658.304Q32679510481.304Q32681607669.283Q32681607669.377Q32681824661.260Q32681824661.282Q32681824661.303Q33135353571.304Q33137450695.283Q3419689062.260 Q3419689062.282 Q3419689062.303 Q3421936230.259 Q3421936230.281 Q3421936230.302 Q37149073081.260Q37149073081.282Q37149073081.303Q38167875878.260Q38167875878.282Q38167875878.303Q38219000533.377Q3848836115.256 Q3850917174.278 Q3851344265.299 Q38753883833.377Q39180574961.260Q39180574961.282Q39180574961.303Q39493696795.347Q39600066516.279Q39600066516.300Q39600066516.347Q39600066516.371Q40249520655.258Q40249520655.279Q42439168719.283Q42439168719.377Q42439443119.260Q42439443119.282Q42439443119.303Q42439443119.350Q42441265899.304Q43507281668.377Q45353769654.278Q45353866761.299Q45360062002.370Q45360108790.346Q46792746863.304Q46794843979.283Q46794843979.377Q47766657548.377Q48118064779.283Q48120161967.304Q50294066187.278Q50294161588.299Q50538125734.377Q50798315515.279Q50798315515.347Q51620582043.279Q51620582043.347Q5265442331.258 Q5265442331.280 Q5265442331.301 Q53380958617.279Q53380958617.300Q53380958617.347Q53380958617.371Q54386358946.377Q55408699622.377Q55415036769.260Q55415036769.282Q55415036769.303Q555331099.346  Q56530976407.283Q56533073587.304Q56854244147.260Q56854244147.282Q56854244147.303Q57228775306.259Q57228775306.281Q57228775306.302Q57230951818.260Q57230951818.282Q57230951818.303Q58004075643.279Q58004075643.347Q58006161095.278Q58008175672.346Q59865321072.260Q59865321072.282Q59865321072.303Q59865321072.350Q59865603600.283Q59865603600.377Q59867700788.304Q59952099962.377Q60071281945.279Q60071281945.300Q60071281945.347Q60071281945.371Q60498678367.377Q61847600945.279Q61847600945.300Q61847600945.347Q61847600945.371Q61955796941.304Q61957894121.283Q6262999707.346 Q6269208676.278 Q64012694200.346Q64016958203.347Q64512216697.346Q64522751110.278Q64681845186.304Q64683667846.260Q64683667846.282Q64683667846.303Q64683667846.350Q64683942374.283Q64683942374.377Q65188245677.377Q6629233134.347 Q67150234539.278Q67151891947.346Q67183863355.279Q67183863355.347Q6771375012.283 Q6773472128.304 Q7522037611.346 Q7528702250.299 Q8395204296.377 Q8971465807.347 Q9153544378.377 Q9214356935.377 Q9356559367.352 Q9356756743.260 Q9356756743.281 Q9633850233.258 Q9633850233.279 Q9644583048.283 Q9644583048.377 Q9646680236.304 Q9870426930.370 Q9870576118.346 Q9876540172.278 00000400800<00@00D00I02b05C07\0:G0=:0@:0C:0F@0IF0IG0IH0LP0O;0Qn0U<0WU0Yn0]C0`^0d30fL0he0kF0mg10Y13S16318[1;;1>J1A_1Dn1GO1Ih1LA1NX1Q91Sb1V_1YY1[n1_61ak1e21gj1jA1lb1oK22D25@27R29l2<>2>S2A42C]2Eo2HA2J[2MT2PJ2Ri2UP2X12ZZ2\g2_<2aI2dQ2gI2j>2mE2mF2mZ2m[2mf2nF30933`34>35935:35;35<35=35B35C35a35b35c36236@38]38^3<Z3>R3B>3F93H@3HA3HB3HG3HO3HP3Hj3Hk3I63I73I83I93J_3KN3L=3LH3LI3Ld3MR3MS3Mg3Ml3Mm3N13N93PR3Rk3SE3T;3T<3T=3T>3T?3U^3V63V;3V<3V=3VB3VC3VD3VO3WC3WT3Wl3Wm3XE3XF3XG3XH3Xc3Xd3Y43Y?3YL3Y^3Yc3Yd3Yh3Yi3Yj3Yo3[F3[G3[L3[V3[W3[X3[Y3^23`K3bl3eM3eQ3eR3f:3h_3i73i<3iG3iO3iP3iQ3mG3mH3mh3mi3mj3mk3nT3o<3o=3o>3o?3o@3oA3oB3oC3oD3oN3oO3oP3oQ40540642O44h44i44j45@46^47747847=47D49]4<64<74<^4<j4<o4=04=14=74=84=94=C4=K4=e4=j4>L4>M4BC4Cn4GM4GN4GO4Ga4Gb4HP4LP4LZ4M04M14M24M34M^4M_4N04N14N24NR4N[4N\4Nk4O24Oa4Ob4Oc4Od4Oe4Of4Og4Oh4Oi4Oj4Ok4Ol4Om4On4Oo4P04P14P24P34P44P54P64P74P84P94P:4P;4PU4PV4PW4PX4PY4PZ4P[4P\4P]4P^4P_4P`4Pa4Pb4Pc4Pd4Pe4Pf4Pg4Ph4Pi4Pj4Pk4Pl4Pm4Pn4Po4Q04Q14Q24Q34Q44QN4Qh4Qi4Qj4Qk4Ql4Qm4Qn4Qo4R04R14R24R34Tc4WY4ZI4]94_l4bY4eH4h04j`4mQ50753055l58b5;;5=\5@55Be5E]5HC5K85N05Pb5S[5VW5YM5[l5^K5a:5d55g35ik5lR5o961S64466U69>6;Y6>@6@g6CR6F96H`6K66MT6Oj6RP6U46W[6Z<6\Z6_86a^6d<6fX6i46kW6n:70L72^75G7807:Q7=:7?[7Ae7Co7F97HC7JM7LW7Na7Q37SE7UW7Wa7Yk7\57^G7`Y7bc7dm7g77iA7iB7iC7iD7iE7iF7iG7k`7nA80Z83;85B87Q89c8<58>?8@I8B^8E38GH8I]8L:8NW8Q88SQ8U[8We8Z78\F8^g8aH8cR8e\8gn8j@8jA8lb8oW92L94\97499U9<69<79<89>Q9A29C<9EF9EG9EH9Ga9JB9L[9O<9Qb9TR9WE9Z29Z39Z49\M9^f9a19c<9eO9gb9j59j69lH9nZ9n[9n\9n]9n^9n_9n`:15:3J:61:8[:;?:=f:@P:C4:Ed:HZ:KJ:KK:KL:KM:M\:P5:RN:Tg:W6:Yi:\_:_O:bL:bM:bN:bO:bP:dZ:fd:i4:kL:n2;0[;3>;5h;88;89;:C;<M;>_;A1;C;;EE;GW;GX;J1;LJ;NT;P^;Rm;Rn;Ro;Ud;Xa;[5;]I;_];_^;__;_`;_a;bJ;dd;gH;io;lP;n_;n`;na;nb;nc;nd<1O<4=<6e<9P<<><>f<@m<C<<EC<GR<GS<GT<GU<GV<GW<GX<GY<Ih<Ii<Ij<Ik<Il<L;<Nh<QU<TJ<W?<Y]<\;<^J<`Q<b`<do<g><iE<k`<nQ=1E=43=6h=9C=;f=>9=>:=@O=Bl=E:=GP=GQ=GR=Io=LD=Nj=Q9=Sb=V?=XW=Zg=]7=_D=aQ=c^=f3=h@=ja=mB=o[S2PPS2PPS2PPS2FBS2FBS3SIGS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB2p34j48'3mg'5pad7'5nodes3SZC2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SPR2F04SP1R3SGBS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SPR2F04SP1R3SGBS1R3HIA4STKn1h2LF2sp2PP3SIG4DALG2bs3LFB3PP03SG03DA03TOP2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02hc3HTc3SP13SZC3SPR2F04SP1R3SGBS1R3HIA4STKn1h2LF2sp2PP3SIG4DALG2bs3LFB3PP03SG03DA03TOP2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02hc3HTc3SP13SZC3SPR2F04SP1R3SGBFFS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SPR4SP1R3SGB4j48'3mg'5pad7'5nodes3SP13SZC2F0S1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB2p34j48'3mg'5pad7'5nodes3SZC2HB5Ha_st5Hl_stS1R3HIA4STKn1h2LF2sp2PP3SIG4DALG2bs3LFB3PP03SG03DA03TOP2FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SPR4SP1R3SGB2h34j48'3mg'5pad7'5nodes3HTc3SP13SZC2F0S1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R3HIA4STKn1h2LF2sp2PP3SIG4DALG2bs3LFB3PP03SG03DA03TOP2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02hc3HTc3SP13SZC3SPR2F04SP1R3SGB2HB5Ha_st5Hl_stS1R3HIA4STKn1h2LF2sp2PP3SIG4DALG2bs3LFB3PP03SG03DA03TOP2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02hc3HTc3SP13SZC3SPR2F04SP1R3SGB2HB5Ha_st5Hl_st2p12L1S1R3HIA4STKn1h2LF2sp2PP3SIG4DALG2bs3LFB3PP03SG03DA03TOP2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02hc3HTc3SP13SZC3SPR2F04SP1R3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB2p34j48'3mg'5pad7'5nodes3SZC2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SPR2F04SP1R3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SPR2F04SP1R3SGB2HB5Ha_st5Hl_st2p12L1S1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SPR2F04SP1R3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3BUF3SIG2bs3LFB3DSB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC2p14APSG3SGB2HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB2p34j48'3mg'5pad7'5nodes3SZC4APSG2HB5Ha_st5Hl_stS1R4STKn2LF2PP3SIG4DALG2lo2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p12L13x283SZC3SGB3APD3x163x293x303x315POST0S1R4STKn2LF2PP3SIG4DALG2lo2bs3LFB2FB3sp11p3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02ES3x143SZC3SGB3APD2x23x153x163x174POSTS1R4STKn2LF2PP3SIG2bs3LFB2D13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2PP3SIG2lo2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p12L13SGB2p34j48'3mg'5pad7'5nodes3x423SZC4APSG3x303x433x443x453x463x474POSTS1R4STKn2LF2PP3SIG2lo2bs3LFB2FB3sp11p3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02ES3x143SZC3APP3SGB2x23x153x163x174POSTS1R4STKn2LF2PP3SIG2lo2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p12L13SGB2p34j48'3mg'5pad7'5nodes3x423SZC3APP3x303x433x443x453x463x474POSTS1R4STKn2LF2PP3SIG2lo2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p12L13x283SZC3APP3SGB3x163x293x303x315POST0S1R4STKn2LF3SIG4DALG2bs3LFB2D33ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SZC4APSG3SGB2HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB2p34j48'3mg'5pad7'5nodes3SZC4APSG2HB5Ha_st5Hl_stS1R4STKn2LF2PP3BUF3SIG2lo2bs3LFB2FB3sp11p3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02ES3x143SZC3SGB3APB2x23x153x163x174POSTS1R4STKn2LF2PP3BUF3SIG2lo2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p12L13x283SZC3SGB3APB3x163x293x303x315POST0S1R4STKn2LF2PP3BUF3SIG2bs3LFB3DPB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3BUF3SIG2bs3LFB3DPB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2PP3BUF3SIG2bs3LFB3DPB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB2D13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF3BUF3SIG2bs3LFB3DSB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGB2p12HB5Ha_st5Hl_stS1R4STKn2LF3BUF3SIG2bs3LFB3DSB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB2p34j48'3mg'5pad7'5nodes3SZC2HB5Ha_st5Hl_stS1R4STKn2LF2PP3SIG4DALG2bs3LFB2D23ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG4DALG2bs3LFB2D23ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG4DALG2bs3LFB2D23ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2PP3SIG2lo2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p12L13x283SZC4APSG3SGB3x163x293x303x315POST0S1R4STKn2LF2PP3SIG2lo2bs3LFB2FB3sp11p3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02ES3x143SZC4APSG3SGB2x23x153x163x174POSTS1R4STKn2LF2PP3SIG2bs3LFB2D13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC2p13SGB2HB5Ha_st5Hl_stS1R4STKn2LF2PP3SIG2bs3LFB2D13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB2p34j48'3mg'5pad7'5nodes3SZC2HB5Ha_st5Hl_stS1R4STKn2LF3SIG4DALG2bs3LFB2D33ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC2p13SGB2HB5Ha_st5Hl_stS1R4STKn2LF3SIG4DALG2bs3LFB2D33ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB2p34j48'3mg'5pad7'5nodes3SZC2HB5Ha_st5Hl_stS1R4STKn2LF2PP3SIG2bs3LFB2D13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB2D13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2PP3SIG2bs3LFB2D13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2lo2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p12L13SGB2p34j48'3mg'5pad7'5nodes3x423SZC4APSG3x303x433x443x453x463x474POSTS1R4STKn2LF2PP3SIG2lo2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p12L13x283SZC3APP3SGB3x163x293x303x315POST0S1R4STKn2LF2PP3SIG2lo2bs3LFB2FB3sp11p3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02ES3x143SZC3APP3SGB2x23x153x163x174POSTS1R4STKn2LF2PP3SIG2lo2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p12L13SGB2p34j48'3mg'5pad7'5nodes3x423SZC3APP3x303x433x443x453x463x474POSTFS2ES2p12L13HL12p42KEFS2p22L23LR2S3END3BUF2bs2B32ES2p12L13HES3HL1S1R4STKn2sp2PP1P3END3BUF3SIG4DALG2bs3PP02B12B32B53SG03DA02FB3sp11p2p13Hp13ACV3SPR2F04SP1R3BCE3SGB4Hp1a2p24Hp2E4Hp2aS1R4STKn2LF2sp2PP1P3END3BUF3SIG4DALG2bs3LFB3PP02B12B32B53SG03DA02FB3sp11p3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SZC3Hp13ACV3SPR2F04SP1R3BCE3SGB4Hp1a2p24Hp2E4Hp2aS1P3END3BUF2B11p2ES2p13Hpc3Hq1S1R4STKn2sp3BUF2lo3slo2bs4SLOS4SLOL3SLO3LOS3sp13SP13ALO3BCEFFFFS3SIGFS1P3END2ES3HES2p22L24Hp2E4NLESFFS3BUF2bs2FB3APBS1R2lo3LOS3ALOS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3SG02FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBFS1R4STKn2LF2sp2PP1P3END3BUF3SIG4DALG2bs3LFB3PP02B12B32B53SG03DA02FB3sp11p3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02ES2p12L13Hp13ACV3SPR4SP1R3BCE3SGB4Hp1a3HL12p22L23Hq24Hp2a4j48'3mg'5pad7'5nodes3SZC2F03ESPS1R4STKn2sp2PP1P3END3BUF3SIG4DALG2bs3PP02B12B32B53SG03DA02FB3sp11p2ES3Hp13HES3ACV3SPR2F04SP1R3BCE3SGB2p12L13LR14Hp1a3HL1S1R4STKn2LF2sp2PP1P3END3BUF3SIG4DALG2bs3LFB3PP02B12B32B53SG03DA02FB3sp11p3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02ES3SZC3Hp13HES3ACV3SPR2F04SP1R3BCE3SGB2p12L13LR14Hp1a3HL1S1R4STKn2LF2sp2PP1P3END3BUF3SIG4DALG2bs3LFB3PP02B12B32B53SG03DA02FB3sp11p3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02ES2p12L13SZC3Hp13HES3ACV3SPR2F04SP1R3BCE3SGB4Hp1a3HL12p22L23LR24Hp2a3HL2S1R4STKn2sp2PP1P3END3BUF3SIG4DALG2bs3PP02B12B32B53SG03DA02FB3sp11p2ES2p12L13Hp13HES3ACV3SPR2F04SP1R3BCE3SGB4Hp1a3HL12p22L23LR24Hp2a3HL2SFS3SIGS2sp3sp1FS1R4STKn2sp2lo3SLO3sp13SP1FS2p22L23LR2FFFS1R4STKn2sp2PP1P3BUF3SIG4DALG2bs3PP02B12B53SG03DA02FB3sp11p2p13Hp13SPR2F04SP1R3SGB4Hp1a2p22L23LR24Hp2aS1R4STKn2sp2PP3SIG4DALG2bs2FB3sp13SGB2p22L23LR2S1R4STKn2sp2PP3SIG4DALG2bs2FB3sp13SGB2p12L13LR1S2p12L13LR1FS1P3END1p2ES3Hpc3HES2p13Hq1S1P1p2ES2p12L13Hp13Hq12p22L23Hq22p33Hq32p43Hq4FS1P3END3BUF2B11p3HpcS3sp1FS2PPS2r13Hr1S1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2sp2lo3SLO3sp13SP1S1R4STKn2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F1FFFFS1R4STKn2sp2PP1P3BUF3SIG4DALG2bs3PP02B12B53SG03DA02FB3sp11p2p13Hp13SPR2F04SP1R3SGB4Hp1a2p24Hp2aS1P3END2ES2p22L23NL03ESPS3SIGSFS3SIGFFS3SIG2xq2X2S1R3HIA4PHIn4CNTn1h1P3END2ES3BUD2p22L25nodes3PSe3PSnS2r23Hr21r2KT1q1HS2ES2p12L13HL12p22L23HL2FS1P3END2ES2p22L23NL03ESPFSFS1R3HIA4STKn1h2sp2lo3TOP2HTSS3BUF3SIG2bs3DSBS2PP3SIG2D1S3SIG2lo4SGLOS2r43Hr41r3KR41q1HS3SIGFS2loFSS3SIGS1R4STKn2sp2PP1P3BUF3SIG4DALG2bs3PP02B12B53SG03DA02FB3sp11p3Hp13SPR2F04SP1R3SGB2p14Hp1aSS3SIGS2PP2xq2X1SSSS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS2FBFS4CNTn1P3END2ES2p22L25nodes4HCNT3CSe3CSnS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3SG02FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS2p12L12p22L23HL22p33Hq3S3SIGS2PP2FB3APPS2r23Hr2FFS1R4STKn2LF2sp2PP1P3END3BUF3SIG4DALG2bs3LFB3PP02B12B32B53SG03DA02FB3sp11p3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13Hp13ACV3SPR4SP1R3BCE3SGB4Hp1a2p22L24Hp2a2p34j48'3mg'5pad7'5nodes3Hq33SZC2F04Hp3EFS3END2ES2p12L13HES3HL12p22L23HL2FFFS1P3END1p2ES2p12L13Hpc3HES3Hq13HL12p23Hq2S4PHIn4CNTn1P3END2ES2p22L25nodes3PSe3PSnFFFFFFFFS1P3END2B2FFFS1R4STKn2sp2lo3slo4SLOS4SLOL3SLO3LOSFS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBFFS3END3BUF2bs2B32ES3HESS1R4STKn2sp2PP1P3BUF3SIG4DALG2bs3PP02B12B53SG03DA02FB3sp11p3Hp13SPR2F04SP1R3SGB2p12L13LR14Hp1aS1R3BUF2lo2bs3LOS3ALO3BCEFS3sp1S2FB2F0S1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBFS1P3END2ES2p12L13HES3HL12p34Hp3E2p43Hq4S3BUF2bs3B47S3SIGFFS1i2HiFFS1R2lo3LOSS2sp3sp1S4PHIn4CNTn1P2ES2p22L23PSeS3SIGS1R4STKn2sp2PP2lo4PPLO3SLO3sp13SP1FS1R4STKn2LF2sp2PP1P3END3BUF3SIG4DALG2bs3LFB3PP02B12B32B53SG03DA02FB3sp11p3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13Hp13ACV3SPR4SP1R3BCE3SGB4Hp1a2p22L24Hp2a2p34j48'3mg'5pad7'5nodes3Hq33SZC2F04Hp3ES1R4STKn2sp2PP1P3END3BUF3SIG4DALG2bs3PP02B12B32B53SG03DA02FB3sp11p3Hp13ACV3SPR2F04SP1R3BCE3SGB2p14Hp1E4Hp1aS1R4STKn2LF2sp2PP1P3END3BUF3SIG4DALG2bs3LFB3PP02B12B32B53SG03DA02FB3sp11p3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3Hp13ACV3SPR2F04SP1R3BCE3SGB2p14Hp1E4Hp1aFFS2r33Hr31r3KR31q1HFS1P3END2ES2p12L13HES3HL12p22L24Hp2E3HL22p33Hq3S1R4STKn2LF2sp2PP1P3END3BUF3SIG4DALG2bs3LFB3PP02B12B32B53SG03DA02FB3sp11p3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p12L13Hp13ACV3SPR4SP1R3BCE3SGB4Hp1a2p22L24Hp2a2p34j48'3mg'5pad7'5nodes3Hq33SZC2F02p43Hq44Hp4ES1P3END2B2S1P3END3BUF2B12p34Hp3ESFFS2FB2r03F641q1r1H2H02q02H43sp14SP1M3SIG3ALSFS2r13Hr11r2KT1q1HFFS4CNTn1P2ES2p22L25nodes4HCNT3CSeS3SIG3SG0SS2sp2lo3sp13SP1S2p22L2S1R4STKn4NAM02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFFFFFFFFFFFFFFFFFFFFFFFFFFS1R4STKn2sp2lo3SLO3sp13SP1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R4STKn2sp2lo3SLO3sp13SP1S1R4STKn2sp2lo3SLO3sp13SP1FFFFFFFFFFFS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_st2p12L1S1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_st2p12L1S1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13ALO3SGB4j48'3mg'5pad7'5nodes3SP13SZC2F1S1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC2p13SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB2p34j48'3mg'5pad7'5nodes3SZC2HB5Ha_st5Hl_stS1R4STKn2LF2sp3BUF3SIG2lo2bs3LFB3SLO3LOS3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13ALO3BCE3SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB3SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO2F13SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO2F13SGB2HB5Ha_st5Hl_st2p12L1S1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO2F13SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC2p13SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB2p34j48'3mg'5pad7'5nodes3SP13SZC2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB4DALO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG4DALG2lo2bs3LFB4DALO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_st2p12L1S1R4STKn2LF2sp3SIG4DALG2lo2bs3LFB4DALO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB3SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO2F13SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO2F13SGB2HB5Ha_st5Hl_st2p12L1S1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO2F13SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3ALO2F13SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3ALO2F13SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13ALO3SGB4j48'3mg'5pad7'5nodes3SP13SZC2F1S1R4STKn2LF2sp2PP3BUF3SIG2lo2bs3LFB3SLO3LOS3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO3BCE3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3BUF3SIG2lo2bs3LFB3SLO3LOS3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO3BCE3SGB2HB5Ha_st5Hl_st2p12L1S1R4STKn2LF2sp3BUF3SIG2lo2bs3LFB3SLO3LOS3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO3BCE3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO2F13SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO2F13SGBS1R4STKn2LF2sp3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF3SIG2lo2bs3LFB4SGLO3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO2F13SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO2F13SGBS1R4STKn2LF2sp3SIG4DALG2lo2bs3LFB4DALO3SLO3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO2F13SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO2F13SGBS1R4STKn2LF2PP3SIG2lo2bs3LFB4PPLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2lo2bs3LFB4PPLO3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2PP3SIG2lo2bs3LFB4PPLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp2PP3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_st2p12L1S1R4STKn2LF2sp3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF3SIG2lo2bs3LFB3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3ALO2F13SGBS1R4STKn2LF3SIG2lo2bs3LFB3LOS2FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3ALO2F13SGBS1R4STKn2LF2sp3SIG4DALG2lo2bs3LFB4DALO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG4DALG2lo2bs3LFB4DALO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3BUF3SIG2lo2bs3LFB3SLO3LOS3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO3BCE3SGBS1R4STKn2LF2sp3BUF3SIG2lo2bs3LFB3SLO3LOS3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO3BCE3SGBS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBFFFFFFS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB2p34j48'3mg'5pad7'5nodes3SZC2HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGB2p12HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB2p34j48'3mg'5pad7'5nodes3SZC2HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCFS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3PP03SG03DA02FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03F643SZC3SPR2F04SP1R3SGBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3PP03SG03DA02FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03F643SZC3SPR2F04SP1R3SGBS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGB2HB5Ha_stS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZC2HB5Ha_stS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO3SGBFFS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBFFS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGB2p12HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB2p34j48'3mg'5pad7'5nodes3SZC2HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB2p34j48'3mg'5pad7'5nodes3SZC2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_st2p12L1S1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stFFS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC4SP1R3SGB2HBS1R4STKn2LF3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC4SP1R3SGB2HBS1R4STKn2LF3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC4SP1R3SGB2HBFS1R4STKn2LF2sp3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBFFFFFFS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_st2p12L1S1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_st2p12L1S1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_st2p12L1S1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stFFFS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB3SLO3LOS3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO3SGB2HB5Ha_st5Hl_st2p12L1S1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3ALO3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3PP03ALS3SG03DA02FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SPR4SP1R3SGB4j48'3mg'5pad7'5nodes3SZC2F0FFFFS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG3slo2bs3LFB4SLOS3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG3slo2bs3LFB4SLOS3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2PP3SIG3slo2bs3LFB4SLOS3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF3SIG3slo2bs3LFB4SLOS3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGB2HB5Ha_st5Hl_st2p12L1S1R4STKn2LF3SIG3slo2bs3LFB4SLOS3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF3SIG3slo2bs3LFB4SLOS3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB2p34j48'3mg'5pad7'5nodes3SZC2HB5Ha_st5Hl_stS1R4STKn2LF3SIG3slo2bs3LFB4SLOS3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBFS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF2PP3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCFS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3ALO3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3ALO3SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCFFS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3PP03ALS3SG03DA02FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SPR2F04SP1R3SGBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3PP03ALS3SG03DA02FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SPR4SP1R3SGB4j48'3mg'5pad7'5nodes3SZC2F0S1R4STKn2LF3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGB2HB5Ha_stS1R4STKn2LF3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGB2HB5Ha_stS1R4STKn2LF3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGB2HB5Ha_stFFFFS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3LOS3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13ALO3SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp2PP3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_st2p12L1S1R4STKn2LF2sp3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCFFFFFS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_st2p12L1S1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_st2p12L1S1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB2HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCFFFFFFFS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCFFFFS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3ALP3PP02FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SPR2F04SP1R3SGBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3ALP3PP02FB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SPR2F04SP1R3SGBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3ALP3PP02FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SPR4SP1R3SGB4j48'3mg'5pad7'5nodes3SZC2F0S1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3ALP3PP02FB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SPR4SP1R3SGB4j48'3mg'5pad7'5nodes3SZC2F0S1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGBS1R3HIA4STKn1h2LF2sp3SIG3slo2bs3LFB3TOP3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC2HT3SGBS1R3HIA4STKn1h2LF2sp2PP3SIG3slo2bs3LFB3TOP3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC2HT3SGB2HB5Ha_st5Hl_stS1R3HIA4STKn1h2LF2sp3SIG3slo2bs3LFB3TOP3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC2HT3SGB2HB5Ha_st5Hl_st2p12L1S1R3HIA4STKn1h2LF2sp3SIG3slo2bs3LFB3TOP3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC2HT3SGB2HB5Ha_st5Hl_stS1R3HIA4STKn1h2LF2sp3SIG3slo2bs3LFB3TOP3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB2p34j48'3mg'5pad7'5nodes3SZC2HT2HB5Ha_st5Hl_stS1R3HIA4STKn1h2LF2sp3SIG3slo2bs3LFB3TOP3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC2HT3SGBS1R3HIA4STKn1h2LF2sp3SIG3slo2bs3LFB3TOP3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZC2HTS1R4STKn2LF3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCFS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF3SIG2bs3LFB3SG03ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC3SGB2HBS1R4STKn2LF3SIG2bs3LFB3SG03ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZC2HBFFS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF3SIG2bs3LFB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p14SP1R3SGB4j48'3mg'5pad7'5nodes3SZCS1R4STKn2LF3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC4SP1R3SGBS1R4STKn2LF3SIG2bs3LFB3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC4SP1R3SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC2F03SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC2F03SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC2F03SGBS1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SZC2F0S1R4STKn2LF3SIG2bs3LFB2FB3ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SZC2F03SGBS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03irt3irp3irl3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q02p13SGB4j48'3mg'5pad7'5nodes3SP13SZCS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13ver3vpd3stg3spd3sl03sq03j482mg4pad73irt3irp3irl3irq3at04apd04aln03aq03bt04bpd04bln03bq03tg04spad4len02q03SP13SZC3SGB". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND FREE GETTAG STKn PHIn_mono FFRn_mono CNTn_mono GETSIG ALGNULL MCI GETNAME SERIAL NAM0 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALS SG0 CWS SGLO DSB ALD DA0 CRDA DALO Q1 Q2 Q3 D1 D2 D3 SLOS SLOL SLO TOP SPA SPH TPV LOS"] Lemma SEG3 : forall (FB sp1 : Z) (w0 w1 w2 lw : word) (k0 k8 kE k16 : word) (jA jB : list byte)
      (p : Z) (ver vpd stg spd : word) (sl0 sq0 : Z) (j48 : list byte) (mg : byte) (pad7 : list byte) (irt irp irl irq : word)
      (at0 apd0 aln0 aq0 bt0 bpd0 bln0 bq0 tg0 spad : word) (len0 q0 : Z) mc moc hc (ES : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    gvS FB sp1 X0 0 0 w0 w1 w2 lw (Z_to_bv 8 0) k0 k8 kE k16 (Z_to_bv 64 DALG) jA jB p
        ([C4 ver; C4 vpd] ++ buf_cells stg spd sl0 sq0 ++ name_blob j48 0 mg pad7 ++ [C4 irt; C4 irp; C8 irl; C8 irq] ++ [C4 at0; C4 apd0; C8 aln0; C8 aq0] ++ [C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0 ++ [C8 (Z_to_bv 64 0)])
        [] mc moc hc ->
    P + 2 <= p -> p <= ES -> ES <= END ->
    havol asegs R HIA h + PHIsi NB <= AVOL_MAX -> hfr asegs R HIA h + FFRsi NB d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 FB) (Z_to_bv 64 SIG) (Z_to_bv 64 PP) (Z_to_bv 64 1) (Z_to_bv 64 ES) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
                      (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x9905c) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until t6. intros D Hp1 Hp2 HES BUD BUDF UW. pose proof D as D0. gvA_open D. rt_facts. walk_prep.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as Dnn.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NAM0 STKn0 NRT; lia).
    pose proof (CNTn_mono 0 NB ltac:(clear - B1 B2; lia)) as CS0'. pose proof (PHIn_mono 0 NB ltac:(clear - B1 B2; lia)) as PS0. pose proof (FFRn_mono 0 NB (d + 1) ltac:(clear - B1 B2; lia)) as FS0.
    assert (NB0 : 0 <= NB) by (clear - B2; lia).
    pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBUF) as OBUFc.
    pose proof (blocks_below_hm R HIA hc _ _ mc _ HHc ltac:(intros b Hb; exact Hb)) as BBc.
    destruct (BBc (BUF, n) ltac:(apply in_or_app; right; exact BIN)) as [_ BCE]. cbn [fst snd] in BCE.
    pose proof (rw_cells_bound _ _ _ _ CSG) as SGB. rewrite SZC in SGB.
    pose proof (F3 BUF n ltac:(apply in_or_app; left; exact BIN)) as APB.
    pose proof (frame_apart_obj0 R HIA LB LF lo DALG 24 FB 64 FRSH CRDA ltac:(clear; lia) ltac:(clear; lia) LOS) as APD.
    lazymatch type of HHc with HM _ _ _ _ ?LBh ?LFh _ =>
      assert (INHq : In (FB, 24) (LBh ++ fdata LFh)) by (apply in_or_app; right; cbn; left; reflexivity);
      assert (INDq : In (FB + 32, 64 - 40) (LBh ++ fdata LFh)) by (apply in_or_app; right; cbn; right; left; reflexivity)
    end.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => pose proof (hm_abase asegs R HIA hc _ _ mx HHc) as ABc end.
    frame_aobj FSH (FB + 32) 1%nat as OL.
    pose proof GETTAG as GT'. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG_G in GT'.
    acallxA_sp sp1
      (eapply GT' with (CS := hcs asegs R HIA hc) (PP := PP) (LENP := FB + 32) (P := p) (END := ES) (BUF := BUF) (bs := bs) (tag := 48) (lo := lo) (lenv := lw);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact OL | exact CSOKc | exact ABc | exact (art_alwf asegs R HIA) | exact OPPc | exact OBUFc | exact B5 | exact ALP | exact PP0 | reflexivity
               | lazymatch goal with
                 | |- rw_cells _ _ PP _ => eassumption
                 | |- rw_cells _ _ (FB + 32) _ => eassumption
                 | |- bytes_at _ _ BUF bs => eassumption
                 | |- stk _ _ lo _ => assumption
                 | |- mem_inv _ _ => assumption
                 | |- BUF <= p => clear - Hpc B1; lia
                 | |- p <= ES => exact Hp2
                 | |- ES <= BUF + n => clear - HES B3; lia
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
               | match goal with |- ?g => idtac "GT1-PRE-LEFT:" g end ]).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "GT1-LEFT:" g end.
    clear GT' ABc OL.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r1 end.
    match goal with H : _ < r1 <= 0 |- _ => rename H into Hr1 end.
    match goal with H : r1 = 0 -> _ |- _ => rename H into HOK1 end.
    match goal with H : p <= ?pp <= ES |- _ => rename H into Hq1; rename pp into p1 end.
    lazymatch goal with H : rw_cells _ ?mx (FB + 32) [C8 ?lq] |- _ => rename lq into L1; rename H into GL1; rename mx into m1 end.
    pose proof (bv_unsigned_in_range 64 L1) as LR1. unfold bv_modulus in LR1. cbn [Z.pow Z.of_N Pos.pow] in LR1.
    assert (Hp1E : P <= p1 <= END) by (clear - Hq1 Hpc HES; lia).
    (* [comment removed for export] *)
    zstep. if_cases KT; zify_cond KT.
    { (* [comment removed for export] *)
      zstep. zstep. intros moq [HKq MFq].
      eapply (OUT R HIA) with (STKn := STKn) (PHIa := 0) (FFRa := 0) (slo := slo) (d := d) (lo := lo) (hc := hc) (mc := m1) (moc := moq) (ar := r1) (nodes := []) (inext := 0)
                               (pre := [C4 ver; C4 vpd] ++ buf_cells stg spd sl0 sq0) (j48 := j48) (mg := mg) (pad7 := pad7)
                               (post := [C4 irt; C4 irp; C8 irl; C8 irq] ++ [C4 at0; C4 apd0; C8 aln0; C8 aq0] ++ [C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0)
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
                 eapply A_pkcs7_signer_C.gvS_mo; [| exact HKq| exact MFq]; unfold A_pkcs7_signer_D.SC, name_blob; repeat rewrite <- app_assoc; cbn [app]; gvA_fin HKc MFc (mo_frame_refl moc))
              | match goal with |- ?g => idtac "SEG3-OUTA1-LEFT:" g end ]. }
    assert (R10 : r1 = 0).
    { first [change 18446744073709551615 with (Z.ones 64) in KT; rewrite ?Z.land_ones in KT by (clear; lia) | idtac]. clear - KT Hr1. Z.div_mod_to_equations. lia. }
    subst r1. destruct (HOK1 eq_refl) as [Hp1a HL1]. clear HOK1 KT Hr1.
    (* [comment removed for export] *)
    unfold buf_cells, name_blob in CSG. cbn [app] in CSG.
    (* [comment removed for export] *)
    do 11 zstep.
    match goal with |- context [Z_to_bv 64 (p1 + bv_unsigned L1)] => idtac | |- ?g => idtac "EI-FORM" end.
    (* [comment removed for export] *)
    do 12 zstep.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HH) as ABc; rename HH into HHc1 end end.
    frame_aobj FSH (FB + 32) 1%nat as OL.
    pose proof GETTAG as GT'. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG_G in GT'.
    lazymatch goal with OPx : aobj _ _ (hcs asegs R HIA hc) _ PP 8, OBx : aobj _ _ (hcs asegs R HIA hc) _ BUF n |- _ =>
    acallxA_sp sp1
      (eapply GT' with (CS := hcs asegs R HIA hc) (PP := PP) (LENP := FB + 32) (P := p1) (END := p1 + bv_unsigned L1) (BUF := BUF) (bs := bs) (tag := 48) (lo := lo) (lenv := L1);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact OL | exact CSOKc | exact ABc | exact (art_alwf asegs R HIA) | exact OPx | exact OBx | exact B5 | exact ALP | exact PP0 | reflexivity
               | lazymatch goal with
                 | |- rw_cells _ _ PP _ => eassumption
                 | |- rw_cells _ _ (FB + 32) _ => eassumption
                 | |- bytes_at _ _ BUF bs => eassumption
                 | |- stk _ _ lo _ => assumption
                 | |- mem_inv _ _ => assumption
                 | |- BUF <= p1 => clear - Hpc Hq1 B1; lia
                 | |- p1 <= p1 + _ => clear - LR1; lia
                 | |- p1 + _ <= BUF + n => clear - HL1 Hq1 HES B3; lia
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
                 | |- _ = Z_to_bv 64 (p1 + bv_unsigned L1) => first [reflexivity | symmetry; apply bv_eq; rewrite ?Z_to_bv_unsigned; reflexivity | match goal with |- ?g => idtac "A1-FORM:" g end]
                 end
               | match goal with |- ?g => idtac "GT2-PRE-LEFT:" g end ])
    end.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "GT2-LEFT:" g end.
    clear GT' ABc OL.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r2 end.
    match goal with H : _ < r2 <= 0 |- _ => rename H into Hr2 end.
    match goal with H : r2 = 0 -> _ |- _ => rename H into HOK2 end.
    match goal with H : p1 <= ?pp <= p1 + _ |- _ => rename H into Hq2; rename pp into p2 end.
    lazymatch goal with H : rw_cells _ ?mx (FB + 32) [C8 ?lq] |- _ => rename lq into L2; rename H into GL2; rename mx into m2 end.
    pose proof (bv_unsigned_in_range 64 L2) as LR2. unfold bv_modulus in LR2. cbn [Z.pow Z.of_N Pos.pow] in LR2.
    assert (Hp2E : P <= p2 <= END) by (clear - Hq1 Hq2 HL1 Hpc HES; lia).
    (* [comment removed for export] *)
    zstep. if_cases KT; zify_cond KT. 2:
    { (* [comment removed for export] *)
      zstep. zstep. intros moq [HKq MFq].
      eapply (OUT R HIA) with (STKn := STKn) (PHIa := 0) (FFRa := 0) (slo := slo) (d := d) (lo := lo) (hc := hc) (mc := m2) (moc := moq) (ar := r2) (nodes := []) (inext := 0)
                               (pre := [C4 ver; C4 vpd] ++ buf_cells stg spd sl0 sq0) (j48 := j48) (mg := mg) (pad7 := pad7)
                               (post := [C4 irt; C4 irp; C8 irl; C8 (Z_to_bv 64 p1)] ++ [C4 at0; C4 apd0; C8 aln0; C8 aq0] ++ [C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0)
                               (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
        first [ sec_hyps | reflexivity | exact UW
              | lazymatch goal with
                | |- name_chain _ _ _ _ _ _ => cbn; reflexivity
                | |- List.NoDup [] => constructor
                | |- _ < r2 <= 0 => clear - Hr2; lia
                | |- havol _ _ _ _ + _ + _ <= _ => cbn [length Z.of_nat]; unfold A_pkcs7_signer_C.PHIsi in BUD; unfold AVOL_CALL in *; clear - BUD PS0 CS0'; nia
                | |- hfr _ _ _ _ + _ + _ <= _ => cbn [length Z.of_nat]; unfold A_pkcs7_signer_C.FFRsi in BUDF; unfold fr_charge in *; clear - BUDF FS0 CS0' Dnn; nia
                | |- 0 + _ <= A_pkcs7_signer_C.PHIsi _ _ _ => cbn [length Z.of_nat]; unfold A_pkcs7_signer_C.PHIsi; unfold AVOL_CALL in *; clear - PS0 CS0'; nia
                | |- 0 + _ <= A_pkcs7_signer_C.FFRsi _ _ _ _ => cbn [length Z.of_nat]; unfold A_pkcs7_signer_C.FFRsi; unfold fr_charge in *; clear - FS0 CS0' Dnn; nia
                end
              | (lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signer_C.gvS] => idtac end end;
                 eapply A_pkcs7_signer_C.gvS_mo; [| exact HKq| exact MFq]; unfold A_pkcs7_signer_D.SC, name_blob; repeat rewrite <- app_assoc; cbn [app]; gvA_fin HKc MFc (mo_frame_refl moc))
              | match goal with |- ?g => idtac "SEG3-OUTA2-LEFT:" g end ]. }
    assert (R20 : r2 = 0).
    { first [change 18446744073709551615 with (Z.ones 64) in KT; rewrite ?Z.land_ones in KT by (clear; lia) | idtac]. clear - KT Hr2. Z.div_mod_to_equations. lia. }
    subst r2. destruct (HOK2 eq_refl) as [Hp2a HL2]. clear HOK2 KT Hr2.
    (* [comment removed for export] *)
    do 15 zstep.
    match goal with |- context [Z_to_bv 64 (p2 + bv_unsigned L2)] => idtac | |- ?g => idtac "EN-FORM" end.
    lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned L2 + p2)] => replace (bv_unsigned L2 + p2) with (p2 + bv_unsigned L2) by (clear; lia) | |- _ => idtac end.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      assert (G2 : gvS FB sp1 X0 0 0 w0 w1 w2 L2 (Z_to_bv 8 0) (Z_to_bv 64 (Z.shiftr (SIG + 112) 3 + al_sb AL)) (Z_to_bv 64 (SIG + 112)) (Z_to_bv 64 (p1 + bv_unsigned L1)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 DALG) jA jB p2
                (([C4 ver; C4 vpd] ++ buf_cells stg spd sl0 sq0) ++ name_blob j48 0 mg pad7 ++ ([C4 irt; C4 irp; C8 irl; C8 (Z_to_bv 64 p1)] ++ [C4 at0; C4 apd0; C8 aln0; C8 aq0] ++ [C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0 ++ [C8 (Z_to_bv 64 0)]))
                [] mx moc hc)
        by (unfold name_blob; repeat rewrite <- app_assoc; cbn [app]; gvA_fin HKc MFc (mo_frame_refl moc))
    end.
    try clear HHc1. try clear PRES. try clear FHD. try clear FSH. try clear SAVE. try clear RSL. try clear STb. try clear PPc. try clear CSG. try clear DAc. try clear BYc. try clear OPP. try clear OSG. try clear ODA. try clear OBUF. try clear SSc. try clear D0. try clear STlo. try clear MIc. try clear GL1. try clear GL2.
    clear CSOKc HT CFBc SCS03c SCS SCSc OPPc OSGc ODAc OBUFc CRP CRS CRDg APP APSG F0 F1 F2 F3 STKH WL WCS WCP CWSc CWPc.
    repeat match goal with H : rw_cells _ _ _ _ |- _ => clear H | H : aobj _ _ _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H | H : sshad _ _ _ _ _ |- _ => clear H end.
    eapply (name_step R HIA) with (PHIn := PHIn) (FFRn := FFRn) (CNTn := CNTn) (STKn := STKn) (hc := hc) (moc := moc) (Lc := []) (p := p2) (ENDx := p2 + bv_unsigned L2) (PHIa := 0) (FFRa := 0) (slo := slo) (d := d) (lo := lo)
                                   (pre32 := [C4 ver; C4 vpd] ++ buf_cells stg spd sl0 sq0) (j48 := j48) (mg := mg) (pad7 := pad7)
                                   (post := [C4 irt; C4 irp; C8 irl; C8 (Z_to_bv 64 p1)] ++ [C4 at0; C4 apd0; C8 aln0; C8 aq0] ++ [C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0 ++ [C8 (Z_to_bv 64 0)])
                                   (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
      first [ exact G2 | exact UW | sec_hyps | reflexivity
            | lazymatch goal with
              | |- p2 <= p2 + _ => clear - LR2; lia
              | |- p2 + _ <= END => clear - HL2 Hq2 HL1 Hq1 HES; lia
              | |- havol _ _ _ _ + 0 + _ <= _ => unfold A_pkcs7_signer_C.PHIsi in BUD; unfold AVOL_CALL in *; clear - BUD CS0'; nia
              | |- hfr _ _ _ _ + 0 + _ <= _ => unfold A_pkcs7_signer_C.FFRsi in BUDF; unfold fr_charge in *; clear - BUDF CS0' Dnn; nia
              | |- 0 <= _ < 2 ^ 64 => clear; lia
              | |- _ mod 2 = 0 => reflexivity
              | |- forall m3 mo3 h3, _ => idtac
              end
            | match goal with |- ?g => idtac "SEG3-NAME-LEFT:" g end ].
    cbv beta. intros m3 mo3 h3 r3 p3 j48' mg' pad7' nodes z0 z1 z2 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 G3 Hr3 Hq3 HRN HNC HND3 HAP3 HCNT HPX3.
    rewrite app_nil_r in G3.
    assert (HNC3 : name_chain asegs (fun _ => True) m3 (SNAME (rev nodes) ++ LB) (hd 0 nodes) nodes).
    { eapply chain_mem; [exact HNC| intros xq Hxq; apply in_or_app; left; apply SNAME_in; exact Hxq| intros xq cs _ HR _; exact HR]. }
    clear HNC HPX3 G2 LAWS KINV.
    try clear HHc. try clear HKc. try clear MFc. try clear HTc. try clear HSc. try clear HFc. try clear HCSc. try clear HVc. try clear HFRc. try clear PRES. try clear SP1. try clear SP1M. try clear F64. try clear FRSH. try clear CFB. try clear FHD. try clear G4. try clear FSH. try clear SAVE. try clear RSL. try clear STb. try clear STlo. try clear PPc. try clear Hpc. try clear CSG. try clear SZC. try clear DAc. try clear BYc. try clear OPP. try clear OSG. try clear ODA. try clear OBUF. try clear MIc. try clear SSc. try clear CSOKc. try clear HT. try clear CFBc. try clear SCS03c. try clear SCS. try clear SCSc. try clear OPPc. try clear OSGc. try clear ODAc. try clear OBUFc. try clear CRP. try clear CRS. try clear CRDg. try clear APP. try clear APSG. try clear F0. try clear F1. try clear F2. try clear F3. try clear STKH. try clear WL. try clear WCS. try clear WCP. try clear CWSc. try clear CWPc.
    pose proof G3 as D. pose proof G3 as D0. gvA_open D. walk_prep.
    unfold buf_cells, name_blob in CSG. cbn [app] in CSG.
    pose proof (AIh_laws asegs R HIA h3) as LAWS. pose proof (KF_kinv asegs R HIA h3 mo3) as KINV.
    pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBUF) as OBUFc.
    assert (Hp3E : P <= p3 <= END) by (clear - Hq3 Hp2E HL2 Hq2 HL1 Hq1 HES; lia).
    (* [comment removed for export] *)
    assert (NLES : p2 + bv_unsigned L2 <= ES) by (clear - HL2 Hq2 HL1 Hq1; lia).
    assert (NL0 : 0 <= p2 + bv_unsigned L2 - p2) by (clear - LR2; lia).
    assert (ESP : p2 + bv_unsigned L2 - p2 <= ES - P /\ ES - P <= NB) by (clear - NLES Hp2E HES; lia).
    pose proof (PHIn_mono (p2 + bv_unsigned L2 - p2) (ES - P) ltac:(clear - NL0 ESP; lia)) as PSe.
    pose proof (FFRn_mono (p2 + bv_unsigned L2 - p2) (ES - P) (d + 1) ltac:(clear - NL0 ESP; lia)) as FSe.
    pose proof (CNTn_mono (p2 + bv_unsigned L2 - p2) (ES - P) ltac:(clear - NL0 ESP; lia)) as CSe.
    pose proof (PHIn_mono (ES - P) NB ltac:(clear - NL0 ESP; lia)) as PSn.
    pose proof (FFRn_mono (ES - P) NB (d + 1) ltac:(clear - NL0 ESP; lia)) as FSn.
    pose proof (CNTn_mono (ES - P) NB ltac:(clear - NL0 ESP; lia)) as CSn.
    assert (HCNTn : Z.of_nat (length nodes) <= CNTsi NB) by (unfold A_pkcs7_signer_C.CNTsi; clear - HCNT CSe CSn; lia).
    assert (CNTE : Z.of_nat (length nodes) <= CNTsi (ES - P)) by (unfold A_pkcs7_signer_C.CNTsi; clear - HCNT CSe; lia).
    assert (PHIE : 0 + PHIn (p2 + bv_unsigned L2 - p2) <= PHIsi (ES - P)) by (unfold A_pkcs7_signer_C.PHIsi; unfold AVOL_CALL in *; clear - PSe CSe; lia).
    assert (FFRE : 0 + FFRn (p2 + bv_unsigned L2 - p2) (d + 1) <= FFRsi (ES - P) d) by (unfold A_pkcs7_signer_C.FFRsi; unfold fr_charge in *; clear - FSe CSe Dnn; nia).
    assert (BUDn : havol asegs R HIA h + (0 + PHIn (p2 + bv_unsigned L2 - p2)) + Z.of_nat (length nodes) * AVOL_CALL <= AVOL_MAX) by (unfold A_pkcs7_signer_C.PHIsi in BUD; unfold AVOL_CALL in *; clear - BUD PSe PSn; lia).
    assert (BUDFn : hfr asegs R HIA h + (0 + FFRn (p2 + bv_unsigned L2 - p2) (d + 1)) + Z.of_nat (length nodes) * fr_charge (d + 1) <= FR_MAX) by (unfold A_pkcs7_signer_C.FFRsi in BUDF; unfold fr_charge in *; clear - BUDF HCNT FSe FSn CSe CSn Dnn; nia).
    assert (PHIn' : 0 + PHIn (p2 + bv_unsigned L2 - p2) + Z.of_nat (length nodes) * AVOL_CALL <= PHIsi NB) by (unfold A_pkcs7_signer_C.PHIsi; unfold AVOL_CALL in *; clear - PSe PSn CSn; lia).
    assert (FFRn' : 0 + FFRn (p2 + bv_unsigned L2 - p2) (d + 1) + Z.of_nat (length nodes) * fr_charge (d + 1) <= FFRsi NB d) by (unfold A_pkcs7_signer_C.FFRsi; unfold fr_charge in *; clear - HCNT FSe FSn CSe CSn Dnn; nia).
    (* [comment removed for export] *)
    zstep. if_cases KR3; zify_cond KR3.
    { (* [comment removed for export] *)
      zstep. intros moq [HKq MFq].
      eapply (OUT R HIA) with (STKn := STKn) (hc := h3) (mc := m3) (moc := moq) (ar := 0) (nodes := nodes) (inext := hd 0 nodes)
                              (pre := [C4 ver; C4 vpd] ++ buf_cells stg spd sl0 sq0) (j48 := j48') (mg := mg') (pad7 := pad7')
                              (post := [C4 irt; C4 irp; C8 irl; C8 (Z_to_bv 64 p1)] ++ [C4 at0; C4 apd0; C8 aln0; C8 aq0] ++ [C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0)
                              (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
        first [ sec_hyps | reflexivity | exact HNC3 | exact HND3 | exact BUDn | exact BUDFn | exact PHIn' | exact FFRn' | exact UW
              | (lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signer_C.gvS] => idtac end end;
                 eapply A_pkcs7_signer_C.gvS_mo; [| exact HKq| exact MFq]; unfold A_pkcs7_signer_D.SC, name_blob in *; repeat rewrite <- app_assoc; cbn [app]; exact D0)
              | lazymatch goal with |- _ < 0 <= 0 => clear; lia end
              | match goal with |- ?g => idtac "SEG3-BF1-LEFT:" g end ]. }
    assert (R30 : r3 = 0).
    { first [change 18446744073709551615 with (Z.ones 64) in KR3; rewrite ?Z.land_ones in KR3 by (clear; lia) | idtac]. clear - KR3 Hr3. Z.div_mod_to_equations. lia. }
    subst r3. clear KR3 Hr3 HRN.
    (* [comment removed for export] *)
    pose proof (presW_init_at R HIA h3 _ _ (SNAME (rev nodes) ++ LB) LF m3 (bv_unsigned sp) (bv_unsigned sp) X0 h HHc
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSc HSc ltac:(clear - LOS SLO NS1 NAM0 STKn0 NRT; lia)) as PRESq.
    assert (WLq : wlow R (SNAME (rev nodes) ++ LB) LF) by (split; [exact (proj2 (proj2 (proj2 PRESq)))| apply (art_data_lo asegs R HIA)]).
    assert (WCSq : wcover R (SNAME (rev nodes) ++ LB) LF (bv_unsigned sp) X0 SIG 200) by (apply wcover_inside; cbn [inside]; right; left; clear; lia).
    assert (WCPq : wcover R (SNAME (rev nodes) ++ LB) LF (bv_unsigned sp) X0 PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    (* [comment removed for export] *)
    do 16 zstep.
    match goal with |- context [Z_to_bv 64 (p3 - p1)] => idtac | |- ?g => idtac "IRL-FORM" end.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    chunk_split CSG 2%nat CV CSG1. chunk_split CSG1 4%nat CSER CREST.
    lazymatch type of CSER with rw_cells _ _ ?a _ => replace a with (SIG + 8) in CSER by (clear; lia) end.
    lazymatch type of CREST with rw_cells _ _ ?a _ => replace a with (SIG + 32) in CREST by (clear; lia) end.
    change (rw_cells asegs _ (SIG + 8) (buf_cells stg spd sl0 sq0)) in CSER || idtac "CSER-FORM".
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ h3 _ _ mx |- _ => pose proof (hm_abase asegs R HIA h3 _ _ mx HH) as ABc end end.
    assert (WCSER : wcover R (SNAME (rev nodes) ++ LB) LF (bv_unsigned sp) X0 (SIG + 8) 24) by (apply wcover_inside; cbn [inside]; right; left; clear; lia).
    pose proof SERIAL as SR'. unfold x509_get_serial_stmtA, A_X509_GET_SERIAL in SR'.
    lazymatch goal with OPx : aobj _ _ (hcs asegs R HIA h3) _ PP 8, OSx : aobj _ _ (hcs asegs R HIA h3) _ SIG 200, OBx : aobj _ _ (hcs asegs R HIA h3) _ BUF n |- _ =>
    acallxA_sp sp1
      (eapply SR' with (CS := hcs asegs R HIA h3) (PP := PP) (SER := SIG + 8) (P := p3) (END := p1 + bv_unsigned L1) (BUF := BUF) (bs := bs) (lo := lo) (tg0 := stg) (pad := spd) (len0 := sl0) (q0 := sq0);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact CSOKc | exact ABc | exact (art_alwf asegs R HIA) | exact OPx | exact OBx | exact B5 | exact ALP | exact PP0 | exact CSER | reflexivity
               | lazymatch goal with
                 | |- rw_cells _ _ PP _ => eassumption
                 | |- bytes_at _ _ BUF bs => eassumption
                 | |- stk _ _ lo _ => assumption
                 | |- mem_inv _ _ => assumption
                 | |- BUF <= p3 => clear - Hp3E B1; lia
                 | |- p3 <= p1 + _ => clear - Hq3 HL2 Hq2; lia
                 | |- p1 + _ <= BUF + n => clear - HL1 Hq1 HES B3; lia
                 | |- BUF + n < 2 ^ 63 => clear - B47; lia
                 | |- PP + 8 <= SIG + 8 \/ _ => clear - D1; lia
                 | |- n = 0 \/ PP + 8 <= BUF \/ _ => right; exact DPB
                 | |- n = 0 \/ SIG + 8 + 24 <= BUF \/ _ => clear - DSB; lia
                 | |- (SIG + 8) mod 8 = 0 => clear - ALS; Z.div_mod_to_equations; lia
                 | |- 0 < SIG + 8 => clear - SG0; lia
                 | |- lo <= sp1 - 64 => unfold STKsg in SLO; clear - SLO SP1 NS1 NAM0 STKn0 NRT; lia
                 | |- alloc_ceiling <= lo => clear - ALO LOS; lia
                 | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                 | |- crange _ lo _ => eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]
                 | |- PP + 8 <= lo \/ _ => left; exact PPLO
                 | |- SIG + 8 + 24 <= lo \/ _ => left; clear - SGLO; lia
                 | |- n = 0 \/ BUF + n <= lo \/ _ => right; left; clear - BCE ALO LOS; lia
                 | |- aobj _ _ _ _ (SIG + 8) 24 => eapply aobj_sub; [exact OSx| clear; lia| clear; lia]
                 end
               | match goal with |- ?g => idtac "SER-PRE-LEFT:" g end ])
    end.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "SER-LEFT:" g end.
    clear SR' ABc.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r4 end.
    match goal with H : _ < r4 <= 0 |- _ => rename H into Hr4 end.
    match goal with H : r4 = 0 -> _ |- _ => rename H into HOK4 end.
    match goal with H : p3 <= ?pp <= p1 + _ |- _ => rename H into Hq4; rename pp into p4 end.
    lazymatch goal with H : rw_cells _ ?mx (SIG + 8) (buf_cells ?tgx spd ?lnx ?qx) |- _ => rename H into CSER5; rename mx into m5; rename tgx into stg5; rename lnx into sl5; rename qx into sq5 | |- _ => idtac "no CSER5" end.
    assert (Hp4E : P <= p4 <= END) by (clear - Hq4 Hp3E HL1 Hq1 HES; lia).
    (* [comment removed for export] *)
    lazymatch goal with CVx : rw_cells _ m5 SIG [C4 ver; C4 vpd], CRx : rw_cells _ m5 (SIG + 32) ?rest |- _ =>
      assert (CSG5 : rw_cells asegs m5 SIG (SC ([C4 ver; C4 vpd] ++ buf_cells stg5 spd sl5 sq5) j48' (hd 0 nodes) mg' pad7'
                       ([C4 irt; C4 irp; C8 (Z_to_bv 64 (p3 - p1)); C8 (Z_to_bv 64 p1)] ++ [C4 at0; C4 apd0; C8 aln0; C8 aq0] ++ [C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0)));
      [ unfold A_pkcs7_signer_D.SC, buf_cells; repeat rewrite <- app_assoc; cbn [app];
        change (rw_cells asegs m5 SIG ([C4 ver; C4 vpd] ++ [C4 stg5; C4 spd; C8 (Z_to_bv 64 sl5); C8 (Z_to_bv 64 sq5)] ++ rest));
        apply rw_cells_join3; [exact CVx| cbn [cells_size csize Nat.add]; replace (SIG + Z.of_nat 8) with (SIG + 8) by (clear; lia); exact CSER5
                              | cbn [cells_size csize Nat.add]; replace (SIG + Z.of_nat 8 + Z.of_nat 24) with (SIG + 32) by (clear; lia); exact CRx]
      | clear CVx CRx CSER5 ]
    | |- _ => idtac "SEG3: no CV/CREST at m5" end.
    assert (G5 : gvS FB sp1 X0 (0 + PHIn (p2 + bv_unsigned L2 - p2)) (0 + FFRn (p2 + bv_unsigned L2 - p2) (d + 1)) w0 w1 w2 L2 (Z_to_bv 8 0) (Z_to_bv 64 (Z.shiftr (SIG + 112) 3 + al_sb AL)) (Z_to_bv 64 (SIG + 112)) (Z_to_bv 64 (p1 + bv_unsigned L1)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 DALG) jA jB p4
                     (SC ([C4 ver; C4 vpd] ++ buf_cells stg5 spd sl5 sq5) j48' (hd 0 nodes) mg' pad7'
                         ([C4 irt; C4 irp; C8 (Z_to_bv 64 (p3 - p1)); C8 (Z_to_bv 64 p1)] ++ [C4 at0; C4 apd0; C8 aln0; C8 aq0] ++ [C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0))
                     (SNAME (rev nodes)) m5 mo3 h3).
    { gvA_fin HKc MFc (mo_frame_refl mo3). }
    assert (HNC5 : name_chain asegs (fun _ => True) m5 (SNAME (rev nodes) ++ LB) (hd 0 nodes) nodes).
    { lazymatch goal with PQ : presW _ _ _ h3 (SNAME (rev nodes) ++ LB) LF _ _ X0 m3 m5 |- _ =>
        eapply (chain_presx asegs L _ _ _ m3 m5 _ _ (bv_unsigned sp) X0);
          [ exact HNC3 | intros xq Hxq; eapply (chain_nodes_in asegs); [exact HNC3| exact Hxq]
          | eapply heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA _ _ _ _ _ _ _ _ PQ))| intros b Hb; apply in_or_app; left; exact Hb| apply Z.le_refl| intros xq Hxq; exact Hxq]
          | unfold NAME_SIZE; clear; lia |];
        intros xq Hx; assert (HxL : In (xq, NAME_SIZE) (SNAME (rev nodes))) by (apply SNAME_in; exact Hx);
        cbn [disjoint_from]; split; [| split; [| exact I]];
        [ pose proof (obj_apart_new R HIA h3 (SNAME (rev nodes)) LB LF ((FB, 64) :: LF) _ lo (htop asegs R HIA h) PP 8 xq NAME_SIZE DIMG HHc ltac:(intros fb Hfb; right; exact Hfb) CWP ltac:(clear - ALO LOS; lia) ltac:(clear; lia) HxL ltac:(unfold NAME_SIZE; clear; lia)) as X1; clear - X1; lia
        | pose proof (obj_apart_new R HIA h3 (SNAME (rev nodes)) LB LF ((FB, 64) :: LF) _ lo (htop asegs R HIA h) SIG 200 xq NAME_SIZE DIMG HHc ltac:(intros fb Hfb; right; exact Hfb) CWS ltac:(clear - ALO LOS; lia) ltac:(clear; lia) HxL ltac:(unfold NAME_SIZE; clear; lia)) as X2; clear - X2; lia ]
      | |- _ => idtac "SEG3: the h3 bundle was dropped" end. }
    (* [comment removed for export] *)
    zstep. if_cases KR4; zify_cond KR4.
    { zstep. intros moq [HKq MFq].
      eapply (OUT R HIA) with (STKn := STKn) (hc := h3) (mc := m5) (moc := moq) (ar := 0) (nodes := nodes)
                              (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
        first [ sec_hyps | reflexivity | exact HNC5 | exact HND3 | exact BUDn | exact BUDFn | exact PHIn' | exact FFRn' | exact UW
              | eapply A_pkcs7_signer_C.gvS_mo; [exact G5| exact HKq| exact MFq]
              | lazymatch goal with |- _ < 0 <= 0 => clear; lia end
              | match goal with |- ?g => idtac "SEG3-BF2-LEFT:" g end ]. }
    assert (R40 : r4 = 0).
    { first [change 18446744073709551615 with (Z.ones 64) in KR4; rewrite ?Z.land_ones in KR4 by (clear; lia) | idtac]. clear - KR4 Hr4. Z.div_mod_to_equations. lia. }
    subst r4. clear KR4 Hr4 HOK4.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases KE; zify_cond KE;
      first [change 18446744073709551615 with (Z.ones 64) in KE; rewrite !Z.land_ones in KE by (clear - Hp4E HL1 Hq1 HES B1 B2 B3 B47 B5; lia) | idtac];
      rewrite ?Z.mod_small in KE by (clear - Hp4E HL1 Hq1 HES B1 B2 B3 B47 B5; lia).
    - (* [comment removed for export] *)
      intros moq [HKq MFq].
      eapply (SEG4 R HIA) with (STKn := STKn) (hc := h3) (mc := m5) (moc := moq) (nodes := nodes) (ES := ES) (p := p4)
                               (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
        first [ sec_hyps | reflexivity | exact HNC5 | exact HND3 | exact HAP3 | exact HCNTn | exact HES | exact BUDn | exact BUDFn | exact PHIn' | exact FFRn' | exact CNTE | exact PHIE | exact FFRE | exact UW
              | eapply A_pkcs7_signer_C.gvS_mo; [exact G5| exact HKq| exact MFq]
              | lazymatch goal with
                | |- P + 2 <= p4 => clear - Hp1 Hq1 Hq2 Hq3 Hq4; lia
                | |- p4 <= ES => clear - KE Hq4 HL1 Hq1; lia
                | |- forall x, In x nodes -> _ => exact HAP3
                end
              | match goal with |- ?g => idtac "SEG3-SEG4-LEFT:" g end ].
    - (* [comment removed for export] *)
      zstep. intros moq [HKq MFq].
      eapply (OUT R HIA) with (STKn := STKn) (hc := h3) (mc := m5) (moc := moq) (ar := 0) (nodes := nodes)
                              (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
        first [ sec_hyps | reflexivity | exact HNC5 | exact HND3 | exact BUDn | exact BUDFn | exact PHIn' | exact FFRn' | exact UW
              | eapply A_pkcs7_signer_C.gvS_mo; [exact G5| exact HKq| exact MFq]
              | lazymatch goal with |- _ < 0 <= 0 => clear; lia end
              | match goal with |- ?g => idtac "SEG3-BF3-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
