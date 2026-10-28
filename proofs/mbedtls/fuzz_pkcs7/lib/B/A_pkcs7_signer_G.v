(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_pkcs7_signer.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag
     A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt A_pkcs7_signer_A A_pkcs7_signer_B A_pkcs7_signer_C A_pkcs7_signer_D A_pkcs7_signer_E A_x509_get_name_stmt
     A_pkcs7_signers_A A_pkcs7_signers_C A_pkcs7_signers_D A_pkcs7_signers_G.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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
  Hypothesis GETNAME : x509_get_name_stmtA asegs R HIA PHIn FFRn CNTn STKn A_X509_GET_NAME.
  Hypothesis NAM0 : 0 <= arl_need_amem R.
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
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
  Let SLOq : lo <= bv_unsigned sp - A_pkcs7_signers_A.STKs R STKn.
  Proof. unfold A_pkcs7_signers_A.STKs. unfold STKsg in SLO. clear - SLO NS1 NAM0 STKn0. lia. Qed.

  (* [comment removed for export] *)
  Ltac sec_hyps :=
    first [ exact IMG | exact UARG | exact SM0 | exact NS1 | exact DIMG | exact HMND | exact CALLOC | exact FREE | exact STKn0 | exact NAM0 | exact GETNAME
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

  #[using="IMG STKn NAM0 CWP PPLO BIN DPB CWS SGLO DSB CRDA DALO D1 D2 D3 SLOS SLOL SLO TOP LOS"] Lemma gvA_acall : forall (FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 kE k16 k24 : word) (jA jB : list byte)
      (p : Z) (sgc : list cell) (Lc : list blk) mc moc hc (pre mid post mid' : list cell) (off k : Z) (m' : mem) (h' : HST asegs R HIA) (p' : Z) (Lc' : list blk) (mo' : Model) (dV dF : Z),
    gvS FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE k16 k24 jA jB p sgc Lc mc moc hc ->
    sgc = pre ++ mid ++ post -> Z.of_nat (cells_size pre) = off -> Z.of_nat (cells_size mid) = k -> cells_size mid' = cells_size mid -> 0 <= off -> off + k <= 200 ->
    (forall x, outside W x -> outside X0 x) ->
    HM asegs R HIA h' (Lc' ++ LB) ((FB, 64) :: LF) m' -> (forall x, hcs asegs R HIA hc x -> hcs asegs R HIA h' x) ->
    htop asegs R HIA h' = htop asegs R HIA hc -> hstkhi asegs R HIA h' = hstkhi asegs R HIA hc -> hflag asegs R HIA h' = hflag asegs R HIA hc ->
    havol asegs R HIA h' <= havol asegs R HIA hc + dV -> hfr asegs R HIA h' <= hfr asegs R HIA hc + dF ->
    HK asegs R HIA h' mo' -> mo_frame moc mo' ->
    presA asegs R (Lc ++ LB) ((FB, 64) :: LF) sp1 sp1 (hstkhi asegs R HIA hc) [(PP, PP + 8); (SIG + off, SIG + off + k)] mc m' ->
    mem_inv asegs m' -> stk asegs m' lo sp1 -> sshad asegs AL m' slo sp1 ->
    rw_cells asegs m' PP [C8 (Z_to_bv 64 p')] -> P <= p' <= END -> rw_cells asegs m' (SIG + off) mid' ->
    gvS FB sp1 W (PHIa + dV) (FFRa + dF) w0 w1 w2 lw b4 k0 k8 kE k16 k24 jA jB p' (pre ++ mid' ++ post) Lc' m' mo' h'.
  Proof.
    intros until dF. intros D Esgc SZp SZm SZm' OFF0 OFFK HWX HH' Ecs Etop Estk Eflag Evol Efr HK' MF' HP' MI' ST' SS' PPc' Hp' CM'.
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
    split; [exact HH'|]. split; [exact HK'|]. split; [eapply mo_frame_trans; [exact MFc| exact MF']|].
    split; [rewrite Etop; exact HTc|]. split; [rewrite Estk; exact HSc|]. split; [rewrite Eflag; exact HFc|].
    split; [intros xq Hx; exact (Ecs xq (HCSc xq Hx))|].
    split; [clear - Evol HVc; lia|]. split; [clear - Efr HFRc; lia|].
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG HMND STKn PHIn_mono FFRn_mono CNTn_mono GETNAME NAM0 LFB ALP PP0 CWP PPLO BIN B1 B3 B47 B5 B30 DPB ALS SG0 CWS SGLO DSB CRDA DALO D1 D2 D3 SLOS SLOL SLO TOP SPA SPH TPV LOS"] Lemma name_step : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 kE k16 k24 : word) (jA jB : list byte)
      (p : Z) (pre32 post : list cell) (j48 : list byte) (mg : byte) (pad7 : list byte) (Lc : list blk) mc moc hc (ENDx RET : Z) (Q : config -> Prop)
      (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
    gvS FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE k16 k24 jA jB p (pre32 ++ name_blob j48 0 mg pad7 ++ post) Lc mc moc hc ->
    cells_size pre32 = 32%nat ->
    p <= ENDx -> ENDx <= END ->
    havol asegs R HIA h + PHIa + PHIn NB <= AVOL_MAX -> hfr asegs R HIA h + FFRa + FFRn NB (d + 1) <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    0 <= RET < 2^64 -> RET mod 2 = 0 ->
    (forall m1 mo1 h1 (r p' : Z) (j48' : list byte) (mg' : byte) (pad7' : list byte) (nodes : list Z) (y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
        (* [comment removed for export] *)
        gvS FB sp1 X0 (PHIa + PHIn (ENDx - p)) (FFRa + FFRn (ENDx - p) (d + 1)) w0 w1 w2 lw b4 k0 k8 kE k16 k24 jA jB p' (pre32 ++ name_blob j48' (hd 0 nodes) mg' pad7' ++ post) (SNAME (rev nodes) ++ Lc) m1 mo1 h1 ->
        -0x3000 < r <= 0 -> p <= p' <= ENDx -> (r <> 0 -> nodes = []) ->
        name_chain asegs (fun _ => True) m1 ((SNAME (rev nodes) ++ Lc) ++ LB) (hd 0 nodes) nodes -> List.NoDup nodes ->
        (forall x, In x nodes -> forall B k, In (B, k) (Lc ++ LB) -> x + NAME_SIZE <= B \/ B + k <= x) ->
        Z.of_nat (length nodes) <= CNTn (ENDx - p) ->
        heap_presx asegs L ((Lc ++ LB) ++ fdata ((FB, 64) :: LF)) sp1 [(PP, PP + 8); (SIG + 32, SIG + 32 + NAME_SIZE)] mc m1 ->
        aevtA asegs (KF asegs R HIA h1 mo1) Q
          (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 sp1) gp tp y0 y1 y2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                   s9v s3v s4v s5v s6v s7v s8v s10v s11v s2v y3 y4 y5 y6)
              F (Z_to_bv 64 RET) fc None m1 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc moc) Q
      (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 PP) (Z_to_bv 64 ENDx) (Z_to_bv 64 (SIG + 32)) a3 a4 a5 a6 a7
               s9v s3v s4v s5v s6v s7v s8v s10v s11v s2v t3 t4 t5 t6)
          F (Z_to_bv 64 A_X509_GET_NAME) fc None mc (seg_rom asegs)).
  Proof.
    intros until s11v. intros D SZ1 HpE HEE BUD BUDF UW RETR RETE KS. pose proof D as D0. gvA_open D. rt_facts. walk_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NAM0 STKn0 NRT; lia).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as Dnn.
    pose proof (CNTn_mono (ENDx - p) NB ltac:(clear - HpE HEE Hpc B1 B2; lia)) as CSm.
    pose proof (PHIn_mono (ENDx - p) NB ltac:(clear - HpE HEE Hpc B1 B2; lia)) as PSm.
    pose proof (FFRn_mono (ENDx - p) NB (d + 1) ltac:(clear - HpE HEE Hpc B1 B2; lia)) as FSm.
    pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBUF) as OBUFc.
    pose proof (rw_cells_bound _ _ _ _ CSG) as SGB. rewrite SZC in SGB.
    (* [comment removed for export] *)
    ddestruct (rw_cells_split3 asegs mc SIG pre32 (name_blob j48 0 mg pad7) post CSG) as (_ & CNB & _). rewrite SZ1 in CNB.
    change (SIG + Z.of_nat 32) with (SIG + 32) in CNB.
    (* [comment removed for export] *)
    assert (UW1 : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA hc) (bv_unsigned sp) sp1 (d + 1)).
    { rewrite HSc.
      assert (UWa : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
      { eapply (uwc_presA R); [exact (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES)| exact UW| clear; lia| | clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO SPR NS1 NAM0 STKn0 NRT; lia].
        intros a Ha. cbn. split; [clear - Ha PPLO LOS SLO NS1 NAM0 STKn0 NRT; lia| split; [clear - Ha SGLO LOS SLO NS1 NAM0 STKn0 NRT; lia| exact I]]. }
      pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UWa| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact Dnn]. }
    destruct (sshad_split asegs AL mc slo sp1 (bv_unsigned sp) SSc ltac:(clear - SP1 SLO SLOL NS1 NAM0 STKn0 NRT; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSlo SShi].
    pose proof GETNAME as GN'. unfold x509_get_name_stmtA in GN'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply GN' with (h := hc) (LB := Lc ++ LB) (LF := (FB, 64) :: LF) (PP := PP) (CUR := SIG + 32) (P := p) (END := ENDx) (BUF := BUF) (bs := bs)
                     (lo := lo) (slo := slo) (d := d + 1) (j48 := j48) (mg := mg) (pad7 := pad7); clear GN';
        rewrite ?(unsigned_lit sp1) by exact SP1R; unfold NAME_SIZE;
        first [ exact HHc | exact HK1 | exact PPc | exact ALP | exact PP0 | exact CWPc | exact PPLO | exact BYc | exact B47 | exact B5 | exact B30 | exact DPB
              | exact STlo | exact SSlo | exact SLOS | exact SLOL | exact MIc | exact TPV | exact UW1 | exact HpE | exact CNB | exact OPPc | exact OBUFc | reflexivity
              | lazymatch goal with
                | |- (length _ <= _)%nat => cbn [length]; clear - LFB; lia
                | |- In (BUF, _) _ => apply in_or_app; right; exact BIN
                | |- BUF <= p => clear - B1 Hpc; lia
                | |- ENDx <= BUF + _ => clear - HEE B3; lia
                | |- List.NoDup _ => exact (HMND _ _ _ _ HHc)
                | |- lo <= sp1 - STKn => unfold STKsg in SLO; clear - SLO SP1 NS1 NAM0 STKn0 NRT; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD HVc PSm; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDF HFRc FSm; lia
                | |- (SIG + 32) mod 8 = 0 => clear - ALS; Z.div_mod_to_equations; lia
                | |- 0 < SIG + 32 => clear - SG0; lia
                | |- aobj _ _ _ _ (SIG + 32) 64 => eapply aobj_sub; [exact OSGc| clear; lia| clear; lia]
                | |- client_wrange _ _ _ _ (SIG + 32) 64 => eapply client_wrange_inside; [exact CWSc| intros b Hb; exact Hb| clear; lia| clear; lia]
                | |- SIG + 32 + 64 <= lo => clear - SGLO; lia
                | |- SIG + 32 + 64 <= BUF \/ _ => clear - DSB; lia
                | |- PP + 8 <= SIG + 32 \/ _ => clear - D1; lia
                end
              | match goal with |- ?g => idtac "NAME-PRE-LEFT:" g end ]. }
    try clear GN'.
    cbv beta. (intros ms2 mo2x dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m3 & mo3 & h3 & r & p' & j48' & mg' & pad7' & nodes
                    & E2 & Ea0 & Hr & MI3 & ST3 & SS3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HCNT & PP3 & Hp' & CNB3 & HNC & HND3 & HAP3 & HH3 & HRN).
    injection E2 as Ems Emo. subst ms2 mo2x ua0.
    rewrite ?(unsigned_lit sp1) in ST3, SS3, HP3 by exact SP1R. unfold NAME_SIZE in HP3.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETR| exact RETE]).
    rewrite (app_assoc (SNAME (rev nodes)) Lc LB) in HH3, HNC.
    assert (G3 : gvS FB sp1 X0 (PHIa + PHIn (ENDx - p)) (FFRa + FFRn (ENDx - p) (d + 1)) w0 w1 w2 lw b4 k0 k8 kE k16 k24 jA jB p'
                     (pre32 ++ name_blob j48' (hd 0 nodes) mg' pad7' ++ post) (SNAME (rev nodes) ++ Lc) m3 mo3 h3).
    { eapply (gvA_acall FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE k16 k24 jA jB p _ Lc mc moc hc pre32 (name_blob j48 0 mg pad7) post (name_blob j48' (hd 0 nodes) mg' pad7') 32 64 m3 h3 p');
        first [ exact D0 | exact HH3 | exact HCS3 | exact HT3 | exact HS3 | exact HF3 | exact HV3 | exact HFR3 | exact HK3 | exact HP3 | exact MI3 | exact ST3 | exact SS3 | exact PP3 | exact CNB3
              | reflexivity | rewrite SZ1; reflexivity | clear; lia | intros xq Hx; exact Hx
              | eapply mo_frame_trans; [exact MF1| exact MF3]
              | clear - Hp' Hpc HpE HEE; lia
              | match goal with |- ?g => idtac "ACALL-LEFT:" g end ]. }
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo3) _ _ _ (conj HK3 (mo_frame_refl mo3))).
    eapply (KS m3 mo3 h3 r p' j48' mg' pad7' nodes);
      [ eapply (A_pkcs7_signer_C.gvS_bud R HIA); [exact G3| clear; lia| clear; lia]
      | exact Hr | exact Hp' | exact HRN | exact HNC | exact HND3 | exact HAP3 | exact HCNT | unfold NAME_SIZE; exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP3) ].
  Qed.
  End Call.
End Walk.
