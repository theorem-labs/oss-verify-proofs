(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_pkcs7_signer.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag
     A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt A_pkcs7_signer_A A_pkcs7_signer_B A_pkcs7_signer_C A_pkcs7_signer_D A_pkcs7_signer_E A_pkcs7_getsig_A A_asn1_get_alg_null_A
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
  Hypothesis NAM0 : 0 <= arl_need_amem R.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55857805827.24000003S1R". (* [comment removed for export] *)
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
    first [ exact IMG | exact UARG | exact SM0 | exact NS1 | exact DIMG | exact HMND | exact CALLOC | exact FREE | exact STKn0 | exact NAM0 | exact GETSIG | exact ALGNULL | exact MCI | exact NBC
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L16526487874.14L19616048289.17L2192452093.13 L22676661558.14L24188363034.14L32883993289.17L38339916114.1700000J00d01701J01a02>02XS1B3bsx2P02Lz3HB12H22H32HLS1B3bsx2P02Lz2H12HL1i2Hi1HS1B3bsx2P02Lz2H12H3S1B3bsx2P02Lz2H22HLS1B3bsx2P02Lz3HB02H12HLS1B3bsx2P02Lz2H12H32HL1i2Hi1HS2mX1B3bsx2P02Lz2HL1i2Hi1H". (* [comment removed for export] *)
  #[using="Type"] Lemma bytes_at_sliceS : forall mX B bsx P0 Lz, bytes_at asegs mX B bsx -> B <= P0 -> 0 <= Lz -> P0 + Lz <= B + Z.of_nat (length bsx) ->
    bytes_at asegs mX P0 (firstn (Z.to_nat Lz) (skipn (Z.to_nat (P0 - B)) bsx))
    /\ Z.of_nat (length (firstn (Z.to_nat Lz) (skipn (Z.to_nat (P0 - B)) bsx))) = Lz.
  Proof.
    clear - HIA. (intros mX B bsx P0 Lz dd_H; ddestruct dd_H as (HB0 & HB1 & HB); intros H1 H2 H3).
    assert (HL : length (firstn (Z.to_nat Lz) (skipn (Z.to_nat (P0 - B)) bsx)) = Z.to_nat Lz).
    { rewrite firstn_length, skipn_length. lia. }
    split; [| rewrite HL; lia]. split; [lia|]. split; [rewrite HL; lia|].
    intros i Hi. rewrite HL in Hi. rewrite nth_error_firstn. destruct (Nat.ltb_spec i (Z.to_nat Lz)); [| lia].
    rewrite nth_error_skipn. rewrite <- (HB (Z.to_nat (P0 - B) + i)%nat) by lia. f_equal. f_equal. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L34603895532.0000001S". (* [comment removed for export] *)
  #[using="IMG NS1 HMND FREE STKn CNTn_mono NAM0 LFB PP0 CWP PPLO BIN B2 ALS SG0 CWS SGLO DSB DA0 CRDA DALO D1 D3 SLOS SLOL SLO TOP SPA SPH TPV"] Lemma BF4 : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 kE k16 k24 : word) (jA jB : list byte)
      (p : Z) (pre : list cell) (j48 : list byte) (inext : Z) (mg : byte) (pad7 : list byte) (post : list cell) (nodes : list Z) mc moc hc
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v s6v s7v s8v : word),
    gvS FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE k16 k24 jA jB p (SC pre j48 inext mg pad7 post) (SNAME (rev nodes)) mc moc hc ->
    cells_size pre = 32%nat -> cells_size post = 96%nat ->
    name_chain asegs (fun _ => True) mc (SNAME (rev nodes) ++ LB) inext nodes -> List.NoDup nodes ->
    havol asegs R HIA h + PHIa + Z.of_nat (length nodes) * AVOL_CALL <= AVOL_MAX ->
    hfr asegs R HIA h + FFRa + Z.of_nat (length nodes) * fr_charge (d + 1) <= FR_MAX ->
    PHIa + Z.of_nat (length nodes) * AVOL_CALL <= PHIsi NB -> FFRa + Z.of_nat (length nodes) * fr_charge (d + 1) <= FFRsi NB d ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 FB) (Z_to_bv 64 SIG) s4v (Z_to_bv 64 1) s6v s7v s8v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
                      (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x99184) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s8v. intros D SZ1 SZ2 HC HND BUD BUDF PHI FFR UW. pose proof D as D0. gvA_open D. rt_facts.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    zstep.
    intros moq [HKq MFq].
    eapply (OUT R HIA) with (STKn := STKn) (PHIa := PHIa) (FFRa := FFRa) (slo := slo) (d := d) (lo := lo) (hc := hc) (mc := mc) (moc := moq) (ar := 0) (nodes := nodes)
                            (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
      first [ sec_hyps | exact SZ1 | exact SZ2 | exact HC | exact HND | exact BUD | exact BUDF | exact PHI | exact FFR | exact UW
            | eapply A_pkcs7_signer_C.gvS_mo; [exact D0| exact HKq| exact MFq]
            | clear; lia
            | match goal with |- ?g => idtac "BF4-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0300@C17025492443.323D37764614195.323D60109446735.323L10113006258.11 L10837002389.2  L12252132089.3  L12480000883.288L12654381620.1  L12727661083.3  L12933749194.12 L13176305223.2  L13358974914.1  L15756354262.7  L15952491317.8  L16477255350.14 L16639068102.288L19902550078.13 L19980016842.7  L21218866939.2  L22162860570.0  L2323623344.12  L23317725208.21 L23555835281.3  L24789587974.11 L25584980021.7  L26211087302.288L27111942217.1  L27291476470.1  L29008468389.288L29010569984.289L29745042132.343L29745045590.344L31099021560.7  L31771379224.289L31863022963.4  L35666023782.13 L35915868660.4  L36021046681.2  L36463206329.4  L36650016793.10 L36864168496.12 L36900630101.0  L38235734261.1  L38308634325.0  L39099741969.3  L39279659947.3  L39332637397.0  L39588638165.0  L39631162845.3  L39685680588.2  L39843502484.22 L4011293537.288 L40228640085.0  L41408890658.3  L41409160545.3  L42193924428.2  L42927756920.1  L44256544967.9  L46881206458.8  L46885531809.3  L47461508865.3  L47528263910.8  L4855685921.0   L48600852026.6  L49037504437.11 L49858401057.0  L50478333068.287L50790731766.13 L51699361186.3  L51977919042.1  L52941874306.3  L5310646197.11  L53840333867.9  L53850825587.7  L54298901339.3  L54553522648.287L55085943702.3  L56380991837.10 L58220375322.8  L58233351431.3  L58566698392.288L58606104182.1  L58780863448.287L58790154276.12 L58972524609.3  L59035441537.3  L59308579414.10 L59462632934.12 L60098763854.6  L60996190382.288L61121862379.17 L64330884479.9  L66151426447.10 L66151427842.16 L66251496775.6  L66526906522.0  L66556294966.11 L67443919320.287L67737097252.2  L8201234081.0   L881835912.0    L9080220944.4   L9356559676.18  L9873114841.13  L9915755099.2   O12200120763.323O1478916974.323 O17025492443.323O1782568635.323 O43849271089.323O45029851139.323O50689527441.323O56414299794.323O59625529265.323O65975700241.323O9930765271.323 P12257878110.323P12721873084.323P21212095580.323P23304868604.323P36465839390.323P41419110342.323P48588551390.323P52940256805.323P54301534716.323P55088519473.323P66237321184.323Q12727161097.295Q13679337060.296Q14336994740.296Q14338872214.295Q14701491822.296Q15766564435.323Q18194786555.296Q18678807790.296Q19372013255.296Q19372378363.297Q21913098889.296Q21915097751.295Q23175730233.296Q24058104442.295Q24203609467.297Q24488471067.297Q24879701787.297Q25393718651.296Q25395567449.295Q26249867834.296Q29441544655.296Q30131525498.295Q30179043846.296Q31124869336.323Q33709800164.296Q34363165844.323Q34964382778.323Q38039133595.296Q38193654267.296Q38195435481.295Q38248387216.323Q38458004507.296Q38704632219.296Q40225809864.323Q41134374863.297Q42127543297.323Q42439168719.323Q4340549784.295 Q44452716678.296Q445366863.297  Q45669463565.295Q48360113622.323Q51975841787.296Q51978213849.295Q52284371310.296Q53372992258.296Q56261435207.296Q56261812603.297Q56691168591.296Q56809641083.296Q58294767598.297Q59321559671.323Q59865603600.323Q60401954810.295Q61431133464.295Q62380812747.323Q63539907919.296Q64683942374.323Q66808104856.295Q7526555924.296 Q7528554762.295 Q8675432942.297 Q9090756535.323 Q9356559660.303 Q9644583048.323 00000103;05\05k06306408B08G08H08f08n09309A09^0:S0=N0><0>T0>U0>V0?50?60?@0?\0?n0B@0BD0BI0BJ0BK0BL0BM0B[0Di0E90ET0Ed0El0Em0F?0F^0F_0Fc0Fd0Fn0G70G80G90GD0GM0HS0Ja0Jb0Jm0Jn0K70K<0KV0L20L30L@0LZ0L[0L\0M60M70P20PV0Pa0Pf0Pg0QA0QY0R10R20TD0TE0T^0U;0U<0WJ0WO0Ya0Z;0ZG0ZT0[00[]0[g0^f0_e0`D0`T0a80a90a:0aT0dO0dP0dQ0dR0da0eP0f30f=0f>0f?0f@0fA0fB0fC0fD0fE0fF0fG0fH0h_0k30k40mH0oc12@15=17Z1:31<I1>l1@m1Bi1Dj1Fk1Fl1I?1I@1IA1K=1M91OG1QU1QV1SW1SX1VB1Xl1Zh1\d1_F1aB1c>1e?1e@1gA1gB1i\1lF1nG20H22S25=27g2:72<82<92>J2@K2BG2DC2FD2HZ2JV2LR2LS2NT2PU2RV2TR2TS2TT2TU2TV2VR2XN2Za2\b2_>2a:2cD2eN2eO2ge2j62lDFS1R3HIA4STKn1h2LF2sp2PP3BUF3SIG4DALG2lo2bs4dlen2dq3LFB3PP03SG03DA03TOP2FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SPR4SP1R3SGB2h24atag4apad4alen2ap3HTc3SP13SZC2F0S1R4STKn2LF2sp2PP3BUF3SIG4DALG2lo2bs4dlen2dq3LFB3LOS2FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS2ES2p22p44Hp4'S3BUF2bsFS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS3BUFFS1R4STKn2sp2PP2lo4PPLO3SLO3SPRS2lo3sp1S3SIGS1R2lo3LOS3ALOS1R3BUF2bs4dlen2dq2Q33ACV3BCES3END3BUF2bs4dlen2B31p2ES3HES2p24alen4Hp2'2ap4Hap22KLS1R4STKn4NAM02LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA04DALO3SLO3SPH2FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SPR4SP1R3SGB4atag4apad4alen2ap3SZC2F0S1R3BUF2lo3slo2bs4dlen2dq2Q34SLOS4SLOL3ALO3BCES1R3HIA1h2sp3TOP3sp13SP1FSS1R4STKn2sp3SIG2lo4SGLO3SLO3SPRFS3SIG2xq1HS1P1p2ES3Hp12p24Hp2'2p44Hp4'S3END3BUF1p2ES3HloS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3SG02FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS2PPS3SIGFFFFS1p2ES2p24Hp2'S1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS2sp3SPH3sp13SP1S1R3HIA4STKn1h2sp2lo3TOP2HTS3BUF3SIG2bs3DSBS2LF3LFBFS2r43Hr41r3KR41q1HS1R4STKn2sp3SIG2lo4SGLO3SLO3SPRSS2loSS3SIG2xq1HS2PP2xq1HSSS2sp2lo3sp1S3SIG3SG0S1R3END3BUF2lo2bs4dlen2B33LOS1p2ES3HES3ALO3BCE2p24alen4Hp2'2ap4Hap22KLS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCSS2PP3SIG2D1FS3SIG3SG0S3SIGS3END3BUF1p2ES3Hlo2p24Hp2'S1P3END1p2ES3Hpc3HES2p24Hp2'FS3SIG2lo4SGLOS3BUF2bs4dlen2dq3B302Q12Q3SFS1R4STKn2sp2lo3SLO3sp13SP1SS1R4STKn4NAM02LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA04DALO3SLO3SPH2FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SPR4SP1R3SGB4atag4apad4alen2ap3SZC2F0S1R4STKn2sp2lo3slo4SLOS4SLOL3SLO3LOSS2PP3SIG2D1S3SIGFS1R4STKn2sp2lo3SLO3sp13SP1S3END3BUF2bs2B31p2ES3HloS3END3BUF2bs2B31p2ES3HloFS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3SG02FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCFS1R3BUF2lo2bs3LOS3ALO3BCES1P3END2ES3HES2p23Hpc2p44Hp4'FS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS3SIGS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3SG02FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2sp2lo3SLO3sp13SP1S3BUF2bs3B47S3SIG2lo4SGLOS1r2Hr2r03K551q1H2r43Hr43K56S3END3BUF2bs2B31p2ES3HES2p24alen4Hp2'2ap4Hap2S1R2lo3LOSS1R4STKn2LF2sp2PP3BUF3SIG4DALG2bs4dlen2dq3LFB3PP03B303SG03DA02Q12Q22Q32FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SPR4SP1R3SGB4atag4apad4alen2ap3SZC2F0S1R3END3BUF2bs4dlen2B31p2ES3HES3ACV3BCE2p24alen4Hp2'2ap4Hap22KLS1P3END3BUF2B11p2ES3Hpc3Hp23HESS1r2Hr2r02KR1q1HS3sp12r04SP1M1q1r1H2H02q02H43SIG3ALSFSS1R4STKn2sp2lo3SLO3sp13SP1S1R4STKn4NAM02LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA04DALO3SLO3SPH2FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SPR4SP1R3SGB4atag4apad4alen2ap3SZC2F0FSSS2sp2lo3sp13SP1S1R4STKn4NAM02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R4STKn2sp2lo3slo4SLOL3SLO3sp13SP1S4alen3ALRFFFFFFFFFFFS1R4STKn2LF2PP3BUF3SIG2lo2bs4dlen2dq3LFB4PPLO3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3BUF3SIG2lo2bs4dlen2dq3LFB4SGLO3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCFS1R4STKn2LF3BUF3SIG2lo2bs4dlen2dq3LFB4SGLO3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3BUF3SIG2lo2bs4dlen2dq3LFB3LOS3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23ALO3BCE3SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3BUF3SIG2lo2bs4dlen2dq3LFB3LOS2FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23ALO3SGB4atag4apad4alen2ap3SZC2F1S1R4STKn2LF3END3BUF3SIG2lo2bs4dlen2dq3LFB2B33LOS3sp11p3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes2ES3SZ13SZ23ALO3BCE3SGB3Hlo2p24atag4apad4alen4Hp2'2ap3SZC4Hap24ALENS1R4STKn2LF3BUF3SIG2lo2bs4dlen2dq3LFB3LOS2FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23ALO3SGB4atag4apad4alen2ap3SZC2F1S1R4STKn2LF3BUF3SIG4DALG2lo2bs4dlen2dq3LFB4DALO3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF2sp3BUF3SIG2lo2bs4dlen2dq3LFB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SP13SZCS1R4STKn2LF3BUF3SIG2lo2bs4dlen2dq3LFB2Q33LOS3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23ALO3BCE3SGB4atag4apad4alen2ap3SZC4DLENS1R4STKn2LF3SIG4DALG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG4DALG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG4DALG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCFS1R4STKn2LF3BUF3SIG2lo2bs4dlen2dq3LFB3LOS3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23ALO3SGB4atag4apad4alen2ap3SZCFFS1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SP13SZCS1R4STKn2LF2sp3SIG2lo2bs3LFB3SLO3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SP13SZCFS1R4STKn2LF3SIG4DALG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCFS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3PP03SG03ALD3DA02FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SPR4SP1R3SGB4atag4apad4alen2ap3SZC2F0S1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3PP03ALS3SG03DA02FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SPR4SP1R3SGB4atag4apad4alen2ap3SZC2F0S1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3ALD3DA02FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SPR4SP1R3SGB4atag4apad4alen2ap3SZC2F0S1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG4DALG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCFS1R4STKn2LF3SIG4DALG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCFS1R4STKn2LF2sp3BUF3SIG2lo2bs4dlen2dq3LFB3SLO3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SP13SZCS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3PP03ALS3SG03DA02FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SPR4SP1R3SGB4atag4apad4alen2ap3SZC2F0S1R4STKn2LF3SIG4DALG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG4DALG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3BUF3SIG2lo2bs4dlen2dq3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3PP03ALS3SG03DA02FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SPR4SP1R3SGB4atag4apad4alen2ap3SZC2F0S1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3PP03SG03ALD3DA02FB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SPR4SP1R3SGB4atag4apad4alen2ap3SZC2F0S1R4STKn2LF3BUF3SIG2lo2bs4dlen2dq3LFB4SGLO3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG4DALG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCFS1R4STKn2LF3BUF3SIG3slo2bs4dlen2dq3LFB4SLOS3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG4DALG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG4DALG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF2sp3BUF3SIG2lo2bs4dlen2dq3LFB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SP13SZCS1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCFS1R4STKn2LF3SIG4DALG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG4DALG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG4DALG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCFFFFS1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF2PP3BUF3SIG2lo2bs4dlen2dq3LFB4PPLO3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3SIG4DALG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R3HIA4STKn1h2LF2sp3BUF3SIG3slo2bs4dlen2dq3LFB3TOP3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZC2HTS1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZCS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SP13SZCS1R4STKn2LF2sp3SIG2lo2bs3LFB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SP13SZCFS1R4STKn2LF2sp3BUF3SIG2lo2bs4dlen2dq3LFB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SP13SZCS1R4STKn2LF3BUF3SIG2bs4dlen2dq3LFB3sp13pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ24SP1R3SGB4atag4apad4alen2ap3SZCS1R4STKn2LF3BUF3SIG2bs4dlen2dq3LFB2FB3pre3j485inext2mg4pad74iraw3bt04bpd04bln03bq03tg04spad4len02q05nodes3SZ13SZ23SGB4atag4apad4alen2ap3SZC2F0". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND FREE STKn CNTn_mono GETSIG ALGNULL MCI NAM0 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALS SG0 CWS SGLO DSB ALD DA0 CRDA DALO Q1 Q2 Q3 D1 D2 D3 SLOS SLOL SLO TOP SPA SPH TPV LOS"] Lemma SEG4 : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 kE : word) (jA jB : list byte)
      (p : Z) (pre : list cell) (j48 : list byte) (inext : Z) (mg : byte) (pad7 : list byte) (iraw : list cell)
      (at0 apd0 aln0 aq0 bt0 bpd0 bln0 bq0 tg0 spad : word) (len0 q0 : Z)
      (nodes : list Z) mc moc hc (ES : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s7v s8v : word),
    gvS FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 DALG) jA jB p
        (SC pre j48 inext mg pad7 (iraw ++ [C4 at0; C4 apd0; C8 aln0; C8 aq0] ++ [C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0)) (SNAME (rev nodes)) mc moc hc ->
    cells_size pre = 32%nat -> cells_size iraw = 24%nat ->
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
                 F (Z_to_bv 64 0x99298) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s8v. intros D SZ1 SZ2 HC HND HAP CNT Hp1 Hp2 HES BUD BUDF PHI FFR CNTE PHIE FFRE UW. pose proof D as D0. gvA_open D. rt_facts. walk_prep.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as Dnn.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NAM0 STKn0 NRT; lia).
    pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBUF) as OBUFc.
    pose proof (blocks_below_hm R HIA hc _ _ mc _ HHc ltac:(intros b Hb; exact Hb)) as BBc.
    destruct (BBc (BUF, n) ltac:(apply in_or_app; right; exact BIN)) as [_ BCE]. cbn [fst snd] in BCE.
    pose proof (rw_cells_bound _ _ _ _ CSG) as SGB. rewrite SZC in SGB.
    assert (Hlo : BUF <= p /\ p <= ES /\ ES <= END) by (clear - Hpc Hp2 HES B1; lia).
    (* [comment removed for export] *)
    assert (Esgc : SC pre j48 inext mg pad7 (iraw ++ [C4 at0; C4 apd0; C8 aln0; C8 aq0] ++ [C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0)
                   = (pre ++ [CB 48 j48; C8 (Z_to_bv 64 inext); C1 mg; CB 7 pad7] ++ iraw) ++ [C4 at0; C4 apd0; C8 aln0; C8 aq0] ++ ([C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0 ++ [C8 (Z_to_bv 64 0)])).
    { unfold A_pkcs7_signer_D.SC. repeat rewrite <- app_assoc. reflexivity. }
    assert (SZP : Z.of_nat (cells_size (pre ++ [CB 48 j48; C8 (Z_to_bv 64 inext); C1 mg; CB 7 pad7] ++ iraw)) = 120).
    { rewrite !cells_size_app, SZ1, SZ2. reflexivity. }
    pose proof CSG as CSG'. rewrite Esgc in CSG'.
    destruct (rw_cells_split3 asegs mc SIG _ _ _ CSG') as (_ & CALG & _). clear CSG'. rewrite SZP in CALG.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    destruct (sshad_split asegs AL mc slo sp1 (bv_unsigned sp) SSc ltac:(clear - SP1 SLO SLOL NS1 NAM0 STKn0 NRT; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSlo SShi].
    pose proof ALGNULL as AN'. unfold asn1_get_alg_null_stmtA, A_ASN1_GET_ALG_NULL in AN'.
    eapply (aevtA_cut_evtA_KF asegs R HIA hc moc).
    { eapply AN' with (h := hc) (LB := SNAME (rev nodes) ++ LB) (LF := (FB, 64) :: LF) (PP := PP) (ALG := SIG + 120) (P := p) (END := ES) (BUF := BUF) (bs := bs) (lo := lo) (slo := slo)
                      (atag := at0) (apad := apd0) (alen := aln0) (apw := aq0);
        first [ exact HHc | exact PPc | exact CALG | exact BYc | exact STlo | exact SSlo | exact SLOS | exact SLOL | exact MIc | exact TPV | exact NS1 | exact NAM0 | exact B5 | exact ALP
              | exact OPPc | exact OBUFc | exact CWPc | idtac ];
        rewrite ?(unsigned_lit sp1) by exact SP1R; unfold ASN1_GET_ALG_NULL_STACK_A;
    first [ eassumption | reflexivity
          | lazymatch goal with
            | |- (length _ < 512)%nat => cbn [length]; unfold LFMAX_CRT in LFB; clear - LFB; lia
            | |- BUF + n < 2 ^ 63 => clear - B47; lia
            | |- PP + 8 <= SIG + 120 \/ _ => clear - D1; lia
            | |- n = 0 \/ PP + 8 <= BUF \/ _ => right; exact DPB
            | |- n = 0 \/ SIG + 120 + 24 <= BUF \/ _ => clear - DSB; lia
            | |- (SIG + 120) mod 8 = 0 => clear - ALS; Z.div_mod_to_equations; lia
            | |- 0 < PP /\ _ => split; [exact PP0| clear - PPLO LOS SLO SPR; lia]
            | |- 0 < SIG + 120 /\ _ => split; [clear - SG0; lia| clear - SGLO LOS SLO SPR; lia]
            | |- lo <= ?sp1 - 4208 => unfold STKsg in SLO; clear - SLO SP1 NS1 NAM0 STKn0 NRT; lia
            | |- lo <= ?sp1 - 304 - arl_need_amem R => unfold STKsg in SLO; clear - SLO SP1 NS1 NAM0 STKn0 NRT; lia
            | |- lo <= ?sp1 - 112 - arl_need_smalloc R => unfold STKsg in SLO; clear - SLO SP1 NS1 NAM0 STKn0 NRT; lia
            | |- ?sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
            | |- ?sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
            | |- ?sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
            | |- PP + 8 <= lo \/ _ => left; exact PPLO
            | |- SIG + 120 + 24 <= lo \/ _ => left; clear - SGLO; lia
            | |- n = 0 \/ BUF + n <= lo \/ _ => right; left; clear - BCE ALO LOS; lia
            | |- client_range _ _ _ PP _ => exact (client_range_of_w L _ _ _ _ _ CWPc)
            | |- client_range _ _ _ (SIG + 120) _ => eapply client_range_inside; [exact CWSc| intros b Hb; exact Hb| clear; lia| clear; lia]
            | |- client_range _ _ _ BUF _ => eapply client_range_block; [apply in_or_app; left; apply in_or_app; right; exact BIN| clear; lia| clear; lia]
            | |- client_wrange _ _ _ _ (SIG + 120) _ => eapply client_wrange_inside; [exact CWSc| intros b Hb; exact Hb| clear; lia| clear; lia]
            | |- aobj _ _ _ _ (SIG + 120) _ => eapply aobj_sub; [exact OSGc| clear; lia| clear; lia]
            | |- _ <= BUF + n => clear - Hlo B3; lia
            | |- BUF <= _ => clear - Hlo B1; lia
            | |- _ <= _ => clear - Hlo; lia
            end
          | match goal with |- ?g => idtac "ALGN-PRE-LEFT:" g end ]. }
    cbv beta. intros ms2 PO.
    ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & h2 & r & p2 & atag & apad & alen & apw
                    & -> & HH2 & Ecs & Etop & Estk & Eflag & Evol & Efr & HKiff & HP2 & MI2 & ST2 & SS2 & Ea0 & Hr & PPc2 & CALG2 & Hp2' & HOK).
    subst ua0. clear AN'.
    replace (ret_pc (Z_to_bv 64 0x992ac)) with (Z_to_bv 64 0x992ac : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in HP2, ST2, SS2 by exact SP1R.
    assert (G2 : gvS FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 DALG) jA jB p2
                     ((pre ++ [CB 48 j48; C8 (Z_to_bv 64 inext); C1 mg; CB 7 pad7] ++ iraw) ++ [C4 atag; C4 apad; C8 alen; C8 apw] ++ ([C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0 ++ [C8 (Z_to_bv 64 0)]))
                     (SNAME (rev nodes)) m2 moc h2).
    { eapply (gvS_pcall R HIA) with (STKn := STKn) (hc := hc) (mc := mc) (mid := [C4 at0; C4 apd0; C8 aln0; C8 aq0]) (off := 120) (k := 24) (p := p)
                                   (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
        first [ sec_hyps | exact HH2 | exact Ecs | exact Etop | exact Estk | exact Eflag | exact Evol | exact Efr | exact HKiff | exact HP2 | exact MI2 | exact ST2 | exact SS2 | exact PPc2 | exact CALG2 | exact SZP
              | eapply (gvS_sgc R HIA); [exact D0| intros CX; rewrite Esgc in CX; exact CX| rewrite <- Esgc; apply SC_size; [exact SZ1| rewrite !cells_size_app, SZ2; reflexivity]]
              | reflexivity | clear; lia | intros xq Hx; exact Hx
              | clear - Hp2' Hpc HES; lia
              | match goal with |- ?g => idtac "PCALL1-LEFT:" g end ]. }
    assert (Esgc2 : (pre ++ [CB 48 j48; C8 (Z_to_bv 64 inext); C1 mg; CB 7 pad7] ++ iraw) ++ [C4 atag; C4 apad; C8 alen; C8 apw] ++ ([C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0 ++ [C8 (Z_to_bv 64 0)])
                    = SC pre j48 inext mg pad7 (iraw ++ [C4 atag; C4 apad; C8 alen; C8 apw] ++ [C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0)).
    { unfold A_pkcs7_signer_D.SC. repeat rewrite <- app_assoc. reflexivity. }
    assert (SZ96 : forall (c4 e4 : list cell), cells_size c4 = 24%nat -> cells_size e4 = 24%nat -> cells_size (iraw ++ c4 ++ e4 ++ buf_cells tg0 spad len0 q0) = 96%nat).
    { intros c4 e4 SZa SZb. rewrite !cells_size_app, SZ2, SZa, SZb. reflexivity. }
    assert (HC2 : name_chain asegs (fun _ => True) m2 (SNAME (rev nodes) ++ LB) inext nodes).
    { eapply (chain_presx asegs L _ _ _ mc m2 _ _ sp1 [(PP, PP + 8); (SIG + 120, SIG + 120 + 24)]);
        [ exact HC | intros xq Hx; eapply (chain_nodes_in asegs); [exact HC| exact Hx]
        | eapply heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP2)| intros b Hb; apply in_or_app; left; exact Hb| apply Z.le_refl| intros xq Hx; exact Hx]
        | unfold NAME_SIZE; clear; lia |].
      intros xq Hx. assert (HxL : In (xq, NAME_SIZE) (SNAME (rev nodes))) by (apply SNAME_in; exact Hx).
      cbn [disjoint_from]. split; [| split; [| exact I]].
      - pose proof (obj_apart_new R HIA hc (SNAME (rev nodes)) LB LF ((FB, 64) :: LF) mc lo (htop asegs R HIA h) PP 8 xq NAME_SIZE DIMG HHc ltac:(intros fb Hfb; right; exact Hfb) CWP ltac:(clear - ALO LOS; lia) ltac:(clear; lia) HxL ltac:(unfold NAME_SIZE; clear; lia)).
        clear - H. lia.
      - pose proof (obj_apart_new R HIA hc (SNAME (rev nodes)) LB LF ((FB, 64) :: LF) mc lo (htop asegs R HIA h) SIG 200 xq NAME_SIZE DIMG HHc ltac:(intros fb Hfb; right; exact Hfb) CWS ltac:(clear - ALO LOS; lia) ltac:(clear; lia) HxL ltac:(unfold NAME_SIZE; clear; lia)).
        clear - H. lia. }
    rewrite Esgc2 in G2.
    clear HHc HKc MFc HTc HSc HFc HCSc HVc HFRc PRES SP1 SP1M F64 FRSH CFB FHD G4 FSH SAVE RSL STb STlo PPc Hpc CSG SZC DAc BYc OPP OSG ODA OBUF MIc SSc D0 HC CALG SSlo SShi OBUFc HP2 MI2 ST2 SS2 PPc2 CALG2.
    clear CSOKc HT CFBc SCS03c SCS SCSc OPPc OSGc ODAc CRP CRS CRDg APP APSG F0 F1 F2 F3 STKH WL WCS WCP CWSc CWPc LAWS KINV.
    apply (aevtA_KF_iff R HIA h2 hc moc _ _ HKiff).
    pose proof G2 as D. pose proof G2 as D0. gvA_open D. walk_prep.
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 moc) as KINV.
    pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBUF) as OBUFc.
    (* [comment removed for export] *)
    pose proof CSG as CSG'. rewrite <- Esgc2 in CSG'.
    destruct (rw_cells_split3 asegs m2 SIG _ _ _ CSG') as (_ & CALG & _). clear CSG'. rewrite SZP in CALG.
    pose proof DAc as DAc'. unfold buf_cells in DAc'.
    (* [comment removed for export] *)
    zstep. if_cases KZ; zify_cond KZ.
    2: {
      zstep. zstep. zstep.
      match goal with |- context [bv_swrap 32 (Z.land r ?o + ?c)] =>
        let v := eval vm_compute in (c - 2^64) in
        replace (bv_swrap 32 (Z.land r o + c)) with (r + v)
          by (symmetry; change o with (Z.ones 64); rewrite Z.land_ones by lia;
              rewrite swrap32_errsum by (clear - Hr; lia); reflexivity) end.
      zstep.
      zstep. if_cases KR; zify_cond KR.
      { intros moq [HKq MFq].
        eapply (BF4 FB sp1 PHIa FFRa) with (hc := h2) (mc := m2) (moc := moq) (nodes := nodes);
          first [ exact SZ1 | apply SZ96; reflexivity | exact HC2 | exact HND | exact BUD | exact BUDF | exact PHI | exact FFR | exact UW
                | eapply A_pkcs7_signer_C.gvS_mo; [exact D0| exact HKq| exact MFq]
                | match goal with |- ?g => idtac "SEG4-BF1-LEFT:" g end ]. }
      exfalso. first [change 18446744073709551615 with (Z.ones 64) in KR; rewrite ?Z.land_ones in KR by (clear; lia) | idtac].
      rewrite ?unsigned_lit in KR by (clear - Hr; lia). clear - KR KZ Hr. Z.div_mod_to_equations. lia. }
    assert (R0 : r = 0).
    { first [change 18446744073709551615 with (Z.ones 64) in KZ; rewrite ?Z.land_ones in KZ by (clear; lia) | idtac]. clear - KZ Hr. Z.div_mod_to_equations. lia. }
    subst r. ddestruct (HOK eq_refl) as (ap & Eap & Hap1 & Hap2). subst apw. clear HOK KZ Hr.
    zstep. zstep. zstep.
    pose proof (bv_unsigned_in_range 64 alen) as ALR. unfold bv_modulus in ALR. cbn [Z.pow Z.of_N Pos.pow] in ALR.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases KT; zify_cond KT.
    { intros moq [HKq MFq].
      eapply (BF4 FB sp1 PHIa FFRa) with (hc := h2) (mc := m2) (moc := moq) (nodes := nodes);
        first [ exact SZ1 | apply SZ96; reflexivity | exact HC2 | exact HND | exact BUD | exact BUDF | exact PHI | exact FFR | exact UW
              | eapply A_pkcs7_signer_C.gvS_mo; [exact D0| exact HKq| exact MFq]
              | match goal with |- ?g => idtac "SEG4-BF2-LEFT:" g end ]. }
    clear KT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases KL; zify_cond KL.
    { intros moq [HKq MFq].
      eapply (BF4 FB sp1 PHIa FFRa) with (hc := h2) (mc := m2) (moc := moq) (nodes := nodes);
        first [ exact SZ1 | apply SZ96; reflexivity | exact HC2 | exact HND | exact BUD | exact BUDF | exact PHI | exact FFR | exact UW
              | eapply A_pkcs7_signer_C.gvS_mo; [exact D0| exact HKq| exact MFq]
              | match goal with |- ?g => idtac "SEG4-BF3-LEFT:" g end ]. }
    first [change 18446744073709551615 with (Z.ones 64) in KL; rewrite !Z.land_ones in KL by (clear - ALR Q1 Q2 Q3 B47 B5; lia) | idtac].
    rewrite ?Z.mod_small in KL by (clear - ALR Q1 Q2 Q3 B47 B5; lia).
    match type of KL with bv_unsigned alen = dlen => idtac | ?t => idtac "KL-FORM:" t end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 362244) with (Z_to_bv 64 (arl_memcmp_i R)) by (rewrite MCI; reflexivity).
    (* [comment removed for export] *)
    pose proof (presW_init_at R HIA h2 _ _ (SNAME (rev nodes) ++ LB) LF m2 (bv_unsigned sp) (bv_unsigned sp) [] h HHc
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSc HSc ltac:(clear - LOS SLO NS1 NAM0 STKn0 NRT; lia)) as PRESq.
    assert (WLq : wlow R (SNAME (rev nodes) ++ LB) LF) by (split; [exact (proj2 (proj2 (proj2 PRESq)))| apply (art_data_lo asegs R HIA)]).
    destruct (bytes_at_sliceS m2 BUF bs ap (bv_unsigned alen) BYc ltac:(exact Hap1) ltac:(clear - ALR; lia) ltac:(clear - Hap2 Hp2' HES B3; lia)) as [ABY ALEN].
    destruct (bytes_at_sliceS m2 BUF bs dq dlen BYc Q1 Q2 Q3) as [DBY DLEN].
    pose proof (artA_bcmp asegs R HIA) as SPB.
    lazymatch type of ABY with bytes_at _ _ _ ?aps => lazymatch type of DBY with bytes_at _ _ _ ?dqs =>
    acallxA_sp sp1
      (eapply SPB with (h := h2) (LB := SNAME (rev nodes) ++ LB) (LF := (FB, 64) :: LF) (P := ap) (Q := dq) (n := dlen) (ps := aps) (qs := dqs) (lo := lo); clear SPB;
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact HHc | exact ABY | exact DBY | exact STlo | exact LOS | exact MIc | reflexivity
               | lazymatch goal with
                 | |- Z.of_nat (length _) = dlen => first [exact DLEN | rewrite ALEN; exact KL]
                 | |- aobj _ _ _ _ ap dlen => eapply aobj_sub; [exact OBUFc| exact Hap1| clear - KL Hap2 Hp2' HES B3; lia]
                 | |- aobj _ _ _ _ dq dlen => eapply aobj_sub; [exact OBUFc| exact Q1| exact Q3]
                 | |- lo <= sp1 - arl_need_bcmp R => unfold STKsg in SLO; clear - SLO SP1 NS1 NAM0 STKn0 NRT NBC; lia
                 | |- crange _ lo _ => eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]
                 | |- ap + dlen <= lo \/ _ => left; clear - KL Hap2 Hp2' HES B3 BCE ALO LOS; lia
                 | |- dq + dlen <= lo \/ _ => left; clear - Q3 BCE ALO LOS; lia
                 | |- dlen = 0 \/ ap + dlen + 8 <= _ => right; clear - KL Hap2 Hp2' HES B3 BCE ACV; lia
                 | |- dlen = 0 \/ dq + dlen + 8 <= _ => right; clear - Q3 BCE ACV; lia
                 | |- dlen < 2 ^ 40 => clear - Q2 Q3 Q1 B30; lia
                 | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                 | |- _ = Z_to_bv 64 dlen => first [reflexivity | rewrite <- KL; symmetry; apply Z_to_bv_bv_unsigned | rewrite <- KL; rewrite Z_to_bv_bv_unsigned; reflexivity | match goal with |- ?g => idtac "A2-FORM:" g end]
                 end
               | match goal with |- ?g => idtac "BCMP-PRE-LEFT:" g end ])
    end end.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "BCMP-LEFT:" g end.
    match goal with H : ?x = Z_to_bv 64 0 <-> _ |- _ => rename H into HBEQ end.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m3 end.
    (* [comment removed for export] *)
    assert (G3 : gvS FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 DALG) jA jB p2
                     (SC pre j48 inext mg pad7 (iraw ++ [C4 atag; C4 apad; C8 alen; C8 (Z_to_bv 64 ap)] ++ [C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0)) (SNAME (rev nodes)) m3 moc h2).
    { gvA_fin HKc MFc (mo_frame_refl moc). }
    assert (HC3 : name_chain asegs (fun _ => True) m3 (SNAME (rev nodes) ++ LB) inext nodes).
    { lazymatch goal with PQ : presW _ _ _ h2 ?LBx LF _ _ _ m2 m3 |- _ =>
        eapply (chain_presx asegs L _ _ _ m2 m3 _ _ (bv_unsigned sp) []);
          [ exact HC2 | intros xq Hxq; eapply (chain_nodes_in asegs); [exact HC2| exact Hxq]
          | eapply heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA _ _ _ _ _ _ _ _ PQ))| intros b Hb; apply in_or_app; left; exact Hb| apply Z.le_refl| intros xq Hxq; exact I]
          | unfold NAME_SIZE; clear; lia | intros; exact I ]
      | |- _ => idtac "SEG4: no m2->m3 bundle for the chain" end. }
    clear PRESq WLq.
    (* [comment removed for export] *)
    zstep. if_cases KB; zify_cond KB.
    { intros moq [HKq MFq].
      eapply (BF4 FB sp1 PHIa FFRa) with (hc := h2) (mc := m3) (moc := moq) (nodes := nodes);
        first [ exact SZ1 | apply SZ96; reflexivity | exact HC3 | exact HND | exact BUD | exact BUDF | exact PHI | exact FFR | exact UW
              | eapply A_pkcs7_signer_C.gvS_mo; [exact G3| exact HKq| exact MFq]
              | match goal with |- ?g => idtac "SEG4-BF4-LEFT:" g end ]. }
    clear KB HBEQ ABY DBY ALEN DLEN CALG DAc'.
    clear HHc HKc MFc HTc HSc HFc HCSc HVc HFRc PRES SP1 SP1M F64 FRSH CFB FHD G4 FSH SAVE RSL STb PPc Hpc CSG SZC DAc BYc OPP OSG ODA OBUF SSc D0 OBUFc.
    try clear STlo. try clear MIc.
    try match goal with H : stk _ m3 lo sp1 |- _ => rename H into STn end. try match goal with H : mem_inv _ m3 |- _ => rename H into MIn end.
    clear CSOKc HT CFBc SCS03c SCS SCSc OPPc OSGc ODAc CRP CRS CRDg APP APSG F0 F1 F2 F3 STKH WL WCS WCP CWSc CWPc.
    pose proof G3 as D. pose proof G3 as D0. gvA_open D. walk_prep.
    try clear STn. try clear MIn.
    pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBUF) as OBUFc.
    (* [comment removed for export] *)
    assert (Esgc3 : SC pre j48 inext mg pad7 (iraw ++ [C4 atag; C4 apad; C8 alen; C8 (Z_to_bv 64 ap)] ++ [C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ buf_cells tg0 spad len0 q0)
                    = (pre ++ [CB 48 j48; C8 (Z_to_bv 64 inext); C1 mg; CB 7 pad7] ++ iraw ++ [C4 atag; C4 apad; C8 alen; C8 (Z_to_bv 64 ap)]) ++ [C4 bt0; C4 bpd0; C8 bln0; C8 bq0] ++ (buf_cells tg0 spad len0 q0 ++ [C8 (Z_to_bv 64 0)])).
    { unfold A_pkcs7_signer_D.SC. repeat rewrite <- app_assoc. reflexivity. }
    assert (SZP3 : Z.of_nat (cells_size (pre ++ [CB 48 j48; C8 (Z_to_bv 64 inext); C1 mg; CB 7 pad7] ++ iraw ++ [C4 atag; C4 apad; C8 alen; C8 (Z_to_bv 64 ap)])) = 144).
    { rewrite !cells_size_app, SZ1, SZ2. reflexivity. }
    pose proof CSG as CSG'. rewrite Esgc3 in CSG'.
    destruct (rw_cells_split3 asegs m3 SIG _ _ _ CSG') as (_ & CALG & _). clear CSG'. rewrite SZP3 in CALG.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    destruct (sshad_split asegs AL m3 slo sp1 (bv_unsigned sp) SSc ltac:(clear - SP1 SLO SLOL NS1 NAM0 STKn0 NRT; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSlo SShi].
    pose proof ALGNULL as AN'. unfold asn1_get_alg_null_stmtA, A_ASN1_GET_ALG_NULL in AN'.
    eapply (aevtA_cut_evtA_KF asegs R HIA h2 moc).
    { eapply AN' with (h := h2) (LB := SNAME (rev nodes) ++ LB) (LF := (FB, 64) :: LF) (PP := PP) (ALG := SIG + 144) (P := p2) (END := ES) (BUF := BUF) (bs := bs) (lo := lo) (slo := slo)
                      (atag := bt0) (apad := bpd0) (alen := bln0) (apw := bq0);
        first [ exact HHc | exact PPc | exact CALG | exact BYc | exact STlo | exact SSlo | exact SLOS | exact SLOL | exact MIc | exact TPV | exact NS1 | exact NAM0 | exact B5 | exact ALP
              | exact OPPc | exact OBUFc | exact CWPc | idtac ];
        rewrite ?(unsigned_lit sp1) by exact SP1R; unfold ASN1_GET_ALG_NULL_STACK_A;
    first [ eassumption | reflexivity
          | lazymatch goal with
            | |- (length _ < 512)%nat => cbn [length]; unfold LFMAX_CRT in LFB; clear - LFB; lia
            | |- BUF + n < 2 ^ 63 => clear - B47; lia
            | |- PP + 8 <= SIG + 144 \/ _ => clear - D1; lia
            | |- n = 0 \/ PP + 8 <= BUF \/ _ => right; exact DPB
            | |- n = 0 \/ SIG + 144 + 24 <= BUF \/ _ => clear - DSB; lia
            | |- (SIG + 144) mod 8 = 0 => clear - ALS; Z.div_mod_to_equations; lia
            | |- 0 < PP /\ _ => split; [exact PP0| clear - PPLO LOS SLO SPR; lia]
            | |- 0 < SIG + 144 /\ _ => split; [clear - SG0; lia| clear - SGLO LOS SLO SPR; lia]
            | |- lo <= ?sp1 - 4208 => unfold STKsg in SLO; clear - SLO SP1 NS1 NAM0 STKn0 NRT; lia
            | |- lo <= ?sp1 - 304 - arl_need_amem R => unfold STKsg in SLO; clear - SLO SP1 NS1 NAM0 STKn0 NRT; lia
            | |- lo <= ?sp1 - 112 - arl_need_smalloc R => unfold STKsg in SLO; clear - SLO SP1 NS1 NAM0 STKn0 NRT; lia
            | |- ?sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
            | |- ?sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
            | |- ?sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
            | |- PP + 8 <= lo \/ _ => left; exact PPLO
            | |- SIG + 144 + 24 <= lo \/ _ => left; clear - SGLO; lia
            | |- n = 0 \/ BUF + n <= lo \/ _ => right; left; clear - BCE ALO LOS; lia
            | |- client_range _ _ _ PP _ => exact (client_range_of_w L _ _ _ _ _ CWPc)
            | |- client_range _ _ _ (SIG + 144) _ => eapply client_range_inside; [exact CWSc| intros b Hb; exact Hb| clear; lia| clear; lia]
            | |- client_range _ _ _ BUF _ => eapply client_range_block; [apply in_or_app; left; apply in_or_app; right; exact BIN| clear; lia| clear; lia]
            | |- client_wrange _ _ _ _ (SIG + 144) _ => eapply client_wrange_inside; [exact CWSc| intros b Hb; exact Hb| clear; lia| clear; lia]
            | |- aobj _ _ _ _ (SIG + 144) _ => eapply aobj_sub; [exact OSGc| clear; lia| clear; lia]
            | |- _ <= BUF + n => clear - Hlo Hp2' B3; lia
            | |- BUF <= _ => clear - Hlo Hp2' B1; lia
            | |- _ <= _ => clear - Hlo Hp2'; lia
            end
          | match goal with |- ?g => idtac "ALGN2-PRE-LEFT:" g end ]. }
    cbv beta. intros ms4 PO.
    ddestruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m4 & h4 & r4 & p4 & btag & bpad & blen & bpw
                    & -> & HH4 & Ecs4 & Etop4 & Estk4 & Eflag4 & Evol4 & Efr4 & HKiff4 & HP4 & MI4 & ST4 & SS4 & Ea0 & Hr4 & PPc4 & CALG4 & Hp4' & HOK4).
    subst va0. clear AN'.
    replace (ret_pc (Z_to_bv 64 0x99384)) with (Z_to_bv 64 0x99384 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in HP4, ST4, SS4 by exact SP1R.
    assert (GQ4 : gvS FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 DALG) jA jB p4
                     ((pre ++ [CB 48 j48; C8 (Z_to_bv 64 inext); C1 mg; CB 7 pad7] ++ iraw ++ [C4 atag; C4 apad; C8 alen; C8 (Z_to_bv 64 ap)]) ++ [C4 btag; C4 bpad; C8 blen; C8 bpw] ++ (buf_cells tg0 spad len0 q0 ++ [C8 (Z_to_bv 64 0)]))
                     (SNAME (rev nodes)) m4 moc h4).
    { eapply (gvS_pcall R HIA) with (STKn := STKn) (hc := h2) (mc := m3) (mid := [C4 bt0; C4 bpd0; C8 bln0; C8 bq0]) (off := 144) (k := 24) (p := p2)
                                   (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
        first [ sec_hyps | exact HH4 | exact Ecs4 | exact Etop4 | exact Estk4 | exact Eflag4 | exact Evol4 | exact Efr4 | exact HKiff4 | exact HP4 | exact MI4 | exact ST4 | exact SS4 | exact PPc4 | exact CALG4 | exact SZP3
              | eapply (gvS_sgc R HIA); [exact D0| intros CX; rewrite Esgc3 in CX; exact CX| rewrite <- Esgc3; apply SC_size; [exact SZ1| apply SZ96; reflexivity]]
              | reflexivity | clear; lia | intros xq Hx; exact Hx
              | clear - Hp4' Hpc HES; lia
              | match goal with |- ?g => idtac "PCALL2-LEFT:" g end ]. }
    assert (Esgc4 : (pre ++ [CB 48 j48; C8 (Z_to_bv 64 inext); C1 mg; CB 7 pad7] ++ iraw ++ [C4 atag; C4 apad; C8 alen; C8 (Z_to_bv 64 ap)]) ++ [C4 btag; C4 bpad; C8 blen; C8 bpw] ++ (buf_cells tg0 spad len0 q0 ++ [C8 (Z_to_bv 64 0)])
                    = SC pre j48 inext mg pad7 ((iraw ++ [C4 atag; C4 apad; C8 alen; C8 (Z_to_bv 64 ap)] ++ [C4 btag; C4 bpad; C8 blen; C8 bpw]) ++ buf_cells tg0 spad len0 q0)).
    { unfold A_pkcs7_signer_D.SC. repeat rewrite <- app_assoc. reflexivity. }
    rewrite Esgc4 in GQ4.
    assert (SZ72 : cells_size (iraw ++ [C4 atag; C4 apad; C8 alen; C8 (Z_to_bv 64 ap)] ++ [C4 btag; C4 bpad; C8 blen; C8 bpw]) = 72%nat) by (rewrite !cells_size_app, SZ2; reflexivity).
    assert (HC4 : name_chain asegs (fun _ => True) m4 (SNAME (rev nodes) ++ LB) inext nodes).
    { eapply (chain_presx asegs L _ _ _ m3 m4 _ _ sp1 [(PP, PP + 8); (SIG + 144, SIG + 144 + 24)]);
        [ exact HC3 | intros xq Hx; eapply (chain_nodes_in asegs); [exact HC3| exact Hx]
        | eapply heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP4)| intros b Hb; apply in_or_app; left; exact Hb| apply Z.le_refl| intros xq Hx; exact Hx]
        | unfold NAME_SIZE; clear; lia |].
      intros xq Hx. assert (HxL : In (xq, NAME_SIZE) (SNAME (rev nodes))) by (apply SNAME_in; exact Hx).
      cbn [disjoint_from]. split; [| split; [| exact I]].
      - pose proof (obj_apart_new R HIA h2 (SNAME (rev nodes)) LB LF ((FB, 64) :: LF) m3 lo (htop asegs R HIA h) PP 8 xq NAME_SIZE DIMG HHc ltac:(intros fb Hfb; right; exact Hfb) CWP ltac:(clear - ALO LOS; lia) ltac:(clear; lia) HxL ltac:(unfold NAME_SIZE; clear; lia)).
        clear - H. lia.
      - pose proof (obj_apart_new R HIA h2 (SNAME (rev nodes)) LB LF ((FB, 64) :: LF) m3 lo (htop asegs R HIA h) SIG 200 xq NAME_SIZE DIMG HHc ltac:(intros fb Hfb; right; exact Hfb) CWS ltac:(clear - ALO LOS; lia) ltac:(clear; lia) HxL ltac:(unfold NAME_SIZE; clear; lia)).
        clear - H. lia. }
    clear HHc HKc MFc HTc HSc HFc HCSc HVc HFRc PRES SP1 SP1M F64 FRSH CFB FHD G4 FSH SAVE RSL STb STlo PPc Hpc CSG SZC DAc BYc OPP OSG ODA OBUF MIc SSc D0 HC3 CALG SSlo SShi OBUFc HP4 MI4 ST4 SS4 PPc4 CALG4 G3.
    clear CSOKc HT CFBc SCS03c SCS SCSc OPPc OSGc ODAc CRP CRS CRDg APP APSG F0 F1 F2 F3 STKH WL WCS WCP CWSc CWPc LAWS KINV.
    apply (aevtA_KF_iff R HIA h4 h2 moc _ _ HKiff4).
    pose proof GQ4 as D. pose proof GQ4 as D0. gvA_open D. walk_prep.
    pose proof (AIh_laws asegs R HIA h4) as LAWS. pose proof (KF_kinv asegs R HIA h4 moc) as KINV.
    (* [comment removed for export] *)
    zstep. if_cases KZ4; zify_cond KZ4.
    2: {
      zstep. zstep. zstep.
      match goal with |- context [bv_swrap 32 (Z.land r4 ?o + ?c)] =>
        let v := eval vm_compute in (c - 2^64) in
        replace (bv_swrap 32 (Z.land r4 o + c)) with (r4 + v)
          by (symmetry; change o with (Z.ones 64); rewrite Z.land_ones by lia;
              rewrite swrap32_errsum by (clear - Hr4; lia); reflexivity) end.
      zstep.
      zstep. if_cases KR4; zify_cond KR4.
      { intros moq [HKq MFq].
        eapply (BF4 FB sp1 PHIa FFRa) with (hc := h4) (mc := m4) (moc := moq) (nodes := nodes);
          first [ exact SZ1 | rewrite cells_size_app, SZ72; reflexivity | exact HC4 | exact HND | exact BUD | exact BUDF | exact PHI | exact FFR | exact UW
                | eapply A_pkcs7_signer_C.gvS_mo; [exact D0| exact HKq| exact MFq]
                | match goal with |- ?g => idtac "SEG4-BF5-LEFT:" g end ]. }
      exfalso. first [change 18446744073709551615 with (Z.ones 64) in KR4; rewrite ?Z.land_ones in KR4 by (clear; lia) | idtac].
      rewrite ?unsigned_lit in KR4 by (clear - Hr4; lia). clear - KR4 KZ4 Hr4. Z.div_mod_to_equations. lia. }
    assert (R40 : r4 = 0).
    { first [change 18446744073709551615 with (Z.ones 64) in KZ4; rewrite ?Z.land_ones in KZ4 by (clear; lia) | idtac]. clear - KZ4 Hr4. Z.div_mod_to_equations. lia. }
    subst r4.
    (* [comment removed for export] *)
    intros moq [HKq MFq].
    eapply (SEG5 R HIA) with (STKn := STKn) (PHIa := PHIa) (FFRa := FFRa) (slo := slo) (d := d) (lo := lo) (hc := h4) (mc := m4) (moc := moq) (nodes := nodes) (ES := ES)
                             (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
      first [ sec_hyps | exact SZ1 | exact SZ72 | exact HC4 | exact HND | exact HAP | exact CNT | exact HES | exact BUD | exact BUDF | exact PHI | exact FFR | exact CNTE | exact PHIE | exact FFRE | exact UW
            | eapply A_pkcs7_signer_C.gvS_mo; [exact D0| exact HKq| exact MFq]
            | clear - Hp1 Hp2 Hp2' Hp4' Hpc; lia
            | match goal with |- ?g => idtac "SEG4-SEG5-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.

(* [comment removed for export] *)
(* [comment removed for export] *)
