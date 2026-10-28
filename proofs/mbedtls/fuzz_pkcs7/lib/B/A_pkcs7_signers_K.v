(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_pkcs7_signers.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag
     A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt A_pkcs7_signers_A A_pkcs7_signers_B A_pkcs7_signers_C A_pkcs7_signers_D A_pkcs7_signers_E A_pkcs7_signers_F A_pkcs7_signers_G A_pkcs7_signers_H A_pkcs7_signers_I A_pkcs7_signers_J.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
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

Local Ltac zchk_fails ::= constr:([0x98e24]).
Local Ltac zchk_new ::= constr:([0x98c34; 0x98c38; 0x98c50; 0x98c58; 0x98c5c; 0x98c6c]).
Local Ltac zchk_unpin ::= repeat match goal with |- context [Z.land ?x 18446744073709551615] =>
  change (Z.land x 18446744073709551615) with (Z.land x (Z.ones 64)); rewrite (Z.land_ones x 64) by (clear; lia) end.
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
  Variables (PHIsi : Z -> Z) (FFRsi : Z -> Z -> Z) (CNTsi : Z -> Z) (STKsi : Z).
  Hypothesis SIGNER : pkcs7_signer_stmtA asegs R HIA PHIsi FFRsi CNTsi STKsi A_PKCS7_SIGNER.
  Hypothesis PHIsi_mono : forall n n', 0 <= n <= n' -> 0 <= PHIsi n <= PHIsi n'.
  Hypothesis FFRsi_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRsi n d <= FFRsi n' d.
  Hypothesis CNTsi_mono : forall n n', 0 <= n <= n' -> 0 <= CNTsi n <= CNTsi n'.
  Hypothesis PHIsi_sadd : forall a b, 0 <= a -> 0 <= b -> PHIsi a + PHIsi b <= PHIsi (a + b).      (* [comment removed for export] *)
  Hypothesis FFRsi_sadd : forall a b d, 0 <= a -> 0 <= b -> FFRsi a d + FFRsi b d <= FFRsi (a + b) d.
  Hypothesis CNTsi_sadd : forall a b, 0 <= a -> 0 <= b -> CNTsi a + CNTsi b <= CNTsi (a + b).
  Hypothesis STKsi0 : 0 <= STKsi.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55853786883.23000003S1R". (* [comment removed for export] *)
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Notation STKs := (A_pkcs7_signers_A.STKs R STKsi).
  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP P END BUF SIG DALG lo slo d : Z) (bs : list byte) (dtg dpad : word) (dlen dq : Z) (sj : signer_junk).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 1)%nat.
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
  Hypothesis SLO : lo <= bv_unsigned sp - STKs.
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
    unfold A_pkcs7_cinfo.A_UAR_GOT, A_fuzz_entry.A_UAR_GOT in UARG; unfold A_SMALLOC_0 in SM0; unfold A_pkcs7_signers_A.STKs in SLO; unfold SIGNER_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation FSH0 :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].


  Local Notation NB := (END - P).
  Local Notation POST := (pkcs7_getsigners_postA asegs R HIA (PHIs PHIsi CNTsi) (FFRs FFRsi CNTsi) (CNTs CNTsi) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP P END SIG DALG NB lo slo d dtg dpad dlen dq m mo0).
  Local Notation X0 := [(PP, PP + 8); (SIG, SIG + 200)].
  Local Notation gvA := (gvA R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP P END BUF SIG DALG lo slo bs dtg dpad dlen dq).

  Ltac gvA_open D :=
    destruct D as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & PRES & SP1 & SP1M & F64 & FRSH & CFB
                   & FHD & G4 & FSH & SAVE & RSL & STb & STlo & PPc & Hpc & CSG & SZC & DAc & BYc & OPP & OSG & ODA & OBUF & MIc & SSc).


  Local Notation sjZ := (SGJ (zeros 80) (Z_to_bv 8 0) (zeros 7) (zeros 96)).





  (* [comment removed for export] *)
  Ltac sec_hyps :=
    first [ exact IMG | exact UARG | exact SM0 | exact NS1 | exact DIMG | exact HMND | exact CALLOC | exact FREE | exact GETTAG | exact SIGNER
          | exact PHIsi_mono | exact FFRsi_mono | exact CNTsi_mono | exact PHIsi_sadd | exact FFRsi_sadd | exact CNTsi_sadd | exact STKsi0
          | exact LFB | exact HPP | exact ALP | exact PP0 | exact CWP | exact PPLO | exact HBY | exact BIN | exact B1 | exact B2 | exact B3 | exact B47 | exact B5 | exact B30 | exact DPB
          | exact HSG | exact ALS | exact SG0 | exact CWS | exact SGLO | exact DSB | exact HDA | exact ALD | exact DA0 | exact CRDA | exact DALO | exact Q1 | exact Q2 | exact Q3
          | exact D1 | exact D2 | exact D3 | exact SLOS | exact SLOL | exact SLO | exact TOP | exact SPA | exact SPH | exact TPV | exact NDL ].

  (* [comment removed for export] *)
  Ltac walk_prep :=
    lazymatch goal with HHc : HM _ _ _ ?hc (?Lc ++ LB) ((?FB, 64) :: LF) ?mc, HTc : htop _ _ _ ?hc = _, HSc : hstkhi _ _ _ ?hc = _, HCSc : forall x, CS x -> hcs _ _ _ ?hc x,
                        CFB : crange CS ?FB 64, FRSH : fresh_apart R LB LF ?FB 64, OPP : aobj _ _ CS ?mc PP 8, OSG : aobj _ _ CS ?mc SIG 200, ODA : aobj _ _ CS ?mc DALG 24,
                        PRES : presW _ _ _ h LB LF _ _ _ m ?mc, SCS0 : crange CS (arl_stklo R) _ |- _ =>
      pose proof (hcs_ok asegs R HIA hc) as CSOKc;
      pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT; rewrite HTc, HSc in HT;
      pose proof (crange_mono _ _ _ _ HCSc CFB) as CFBc;
      pose proof (crange_mono _ _ _ _ HCSc SCS0) as SCS03c;
      assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 STKsi0 NRT TOP HT; lia]);
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

  (* [comment removed for export] *)
  Ltac gvA_fin HK9 MFc MF9 :=
    lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signers_C.gvA] => idtac end end;
    lazymatch goal with HTc : htop _ _ _ ?hc = _, HSc : hstkhi _ _ _ ?hc = _, HFc : hflag _ _ _ ?hc = _, HCSc : forall x, CS x -> hcs _ _ _ ?hc x,
                        HVc : havol _ _ _ ?hc <= _, HFRc : hfr _ _ _ ?hc <= _ |- _ =>
      split; [cbn [app]; eassumption|]; split; [exact HK9|]; split; [eapply mo_frame_trans; [exact MFc| exact MF9]|];
      split; [exact HTc|]; split; [exact HSc|]; split; [exact HFc|]; split; [exact HCSc|]; split; [exact HVc|]; split; [exact HFRc|];
      split; [eassumption|];
      repeat match goal with |- _ /\ _ => split end;
      first [ eassumption | reflexivity
            | lazymatch goal with |- rw_cells _ ?mx SIG _ => lazymatch goal with CE : rw_cells _ mx SIG _ |- _ => unfold signer_cells; cbn [sj0 sj_merged sj1 sj2 app]; exact CE end end
            | match goal with H : ?a <= ?x <= ?b |- ?a' <= ?x' => first [exact (proj1 H) | exact (proj2 H)] end
            | match goal with |- ?g => idtac "GVA-FIN-LEFT:" g end ]
    end.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L29367582956.10600000OS2LF2sp2PP3SIG4DALG2bs3LFB2ns1r". (* [comment removed for export] *)
  #[using="LF sp PP SIG DALG bs LFB"] Lemma len_sb_cons : forall x ns r, length (signer_blocks ((x, ns) :: r)) = (length ns + 1 + length (signer_blocks r))%nat.
  Proof. intros. cbn [signer_blocks fst snd]. rewrite !length_app, length_map. cbn [length]. unfold blk in *. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma len_sb_nil : length (signer_blocks []) = 0%nat.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Ltac budlia keep :=
    rewrite ?len_sb_cons, ?len_sb_nil in *; cbn [length] in *; rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ in *;
    change (Z.of_nat 0) with 0 in *; change (Z.of_nat 1) with 1 in *; unfold blk, AVOL_CALL, fr_charge in *; keep; lia.

  Ltac kz2 KZ HP2 C2 :=
    unfold SIGNER_SIZE, NAME_SIZE in HP2, C2;
    first [change 18446744073709551615 with (Z.ones 64) in KZ; rewrite Z.land_ones in KZ by (clear; lia) | idtac];
    rewrite ?Z.mod_small in KZ by (clear - HP2 C2; pose proof (alloc_ceiling_val R); lia); rewrite ?unsigned_lit in KZ by (clear - HP2 C2; pose proof (alloc_ceiling_val R); lia).




  (* [comment removed for export] *)
  Local Notation OPENA := (OPENA R LB LF BUF bs).
  Local Notation CIT := (PHIsi NB + 2 * 200 + 2 * AVOL_CALL).
  Local Notation FIT := (FFRsi NB (d + 1) + 2 * fr_charge (d + 1)).
  (* [comment removed for export] *)
  Local Notation SINV := (A_pkcs7_signers_C.SINV PHIsi FFRsi CNTsi).

  (* [comment removed for export] *)
  Definition LOOPST (kk : nat) : Prop :=
    forall (ES p cnt : Z) (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (s3v : word) (j32 : list byte)
      (inext0 : Z) (names0 : list Z) (sjh : signer_junk) (S1 : Z) (mid : list (Z * list Z)) (prev pinext : Z) (pnames : list Z) (psj : signer_junk)
      (Lc : list blk) mc moc hc
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s8v : word),
    ES - p <= Z.of_nat kk -> P < p -> p < ES -> ES <= END -> 1 <= cnt -> cnt <= p - P ->
    gvA FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 (Z_to_bv 64 (-22400)) (Z_to_bv 64 SIG) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 DALG) j32 p (signer_cells inext0 S1 sjh) Lc mc moc hc ->
    OPENA mc Lc inext0 names0 S1 mid prev pinext pnames psj ->
    SINV d (p - P) cnt PHIa FFRa (Z.of_nat (length Lc)) ->
    havol asegs R HIA h + PHIs PHIsi CNTsi NB <= AVOL_MAX -> hfr asegs R HIA h + FFRs FFRsi CNTsi NB d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 FB) s3v (Z_to_bv 64 cnt) (Z_to_bv 64 prev) (Z_to_bv 64 PP) (Z_to_bv 64 (al_sb AL)) s8v (Z_to_bv 64 FB)
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 ES) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x98c08) fc None mc (seg_rom asegs)) moc).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0170@L11447729963.24 L11709836466.1  L12230302151.15 L13641031927.3  L17146782949.8  L20789541055.1  L21611099214.4  L21901341486.6  L22369917680.15 L23673171628.3  L2692963558.3   L27111942217.1  L2821352801.17  L35666023782.12 L38308634325.0  L39021626863.15 L39076636629.0  L39280637297.0  L39332637397.0  L40228640085.0  L41202929119.262L41354231767.261L42439184590.3  L42609104409.264L42927756920.1  L43079821192.3  L43641669034.4  L44482819349.3  L44921588402.0  L46091134646.15 L46890497670.7  L48132467214.13 L48384377398.16 L49493397620.5  L50897094000.17 L52783262018.3  L53947033437.3  L56734347951.4  L569552768.264  L58971104604.2  L59314873579.2  L59314955108.1  L59321314285.2  L60098763854.6  L64687743334.14 L64935916434.1  L6990800330.3   L7149751374.15  L7419122673.264 L8272585790.10  L881835912.0    L9631767084.2   Q10468075293.279Q10649498890.271Q10651763983.270Q11801279589.263Q13733158450.270Q17619896906.278Q17701933584.271Q20789718111.278Q20800531708.259Q20802671481.279Q28098852862.262Q37591829852.262Q42340767550.261Q44958253612.260Q45353686192.270Q48068362337.279Q60290812962.279Q61847600945.271Q66567033589.25900000a00g01801G01\01b02302H02c03103A03E04;04W04X04e04f04g04h04i06307K07W0:E0:J0:Y0:g0;50;60;B0;b0<K0=?0=I0>10>?0>J0>V0@V0@a0@g0@j0A30A=0AZ0A`0An0BE0E:0Ec0Ed0Ek0F\0GK0H:0I=0Il0J]0KL0L=0Ln0M_0Nb0Oe0P_0QX0RG0RH0TM0Ui0VZS3cnt3Hc15CNT301q1r1H2H02q02r02r12H42H52q12H93H10S4prevS2kk2ES2p'3Hp32KES3SIG4prev4APVSS5CNTsi1P3END3Lc23SB1S4prevS3BUF2bs4prev3PVBS1P3END2ES2p'3Hp33HESS1P2kk1p2p'3cnt3Hp23Hc13Hc2S2PP4prev4APVPS4DALG4prev4APVDS2PPS1R5STKsi2sp2lo3slo4SLOS4SLOL3SLO3sp14prev3SP13ALO3PCES1R3HIA5STKsi1h2sp2lo3TOP2HTSS2kk2ES2p'2HkSSSSS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB2kk2FB3sp16inext03sjh2S14prev2Sn3Lc23SZCS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB2kk3cnt2FB3sp16inext03sjh2S14prev2Sn3Hc13Lc23SZC5CNT30S1R3slo4SLOSS1R5STKsi2LF2sp2PP1P3END3BUF3SIG4DALG2lo2bs3LFB3PP02B12B33B472B53SG03DA03SLO3LOS2kk1p2p'2FB3sp16inext03sjh2S14prev2Lc2Sn6nodes23Hp13Hp23Lc23SP13SZC4PPOS2NP3ALO3ACV3SPR2F03NBpS3SIGS3cnt3Hc15CNT30S1P3END2p'3NBpS2FB4prev4APVFSS2kk3cnt3Hc1S5PHIsi5CNTsi1P3END4PHIa3SB23PSrS1R3NS15STKsi2sp2lo3slo4SLOS4SLOL3SLO3ALOS1P3END3BUF2bs2B12B33B302ES1p2p'3cnt3Hp23Hp33HES3Hc2S1P3END2B2S1R3NS15STKsi2sp2lo3SLO3LOS4prev3ALO3PCES4prev2Sn4APVNS4prev1a2HaS4prev1x1k1XS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS2kk2FB3sp16inext03sjh2S14prev2Sn3Lc23SP13SZC4PPOS2NP3ALO3ACV3SPR2F03PCES2Lc6nodes2S2Sn1HS1ES2Sn4APVNS1R2lo3LOSS1R3HIA5STKsi1h2sp3slo3TOP2HTS4prevS2FB4prev4APVFS1P2kk1p2p'3cnt3Hp23Hc2S1R5STKsi2LF2sp2PP1P3END3BUF3SIG4DALG2lo2bs3LFB3PP02B12B33B472B53SG03DA03SLO3LOS2kk2ES1p2p'2FB3sp16inext03sjh2S14prev2Lc2Sn6nodes23Hp13Hp23Hp33HES3Lc23SP13SZC4PPOS2NP3ALO3ACV3SPR2F0S5FFRsi5CNTsi1P3END1d4FFRa3Dnn3SB33FSr2L3SS2FB2F0S1R5STKsi2LF2bs3LFB2kk6inext03sjh2S14prev3Lc23SZCS1R5STKsi2LF2PP2bs3LFB2kk6inext03sjh2S13Lc23SZCS1R5STKsi2LF2PP2bs3LFB2kk6inext03sjh2S13Lc23SZCS1R5STKsi2LF2bs3LFB2kk6inext03sjh2S14prev2Sn3Lc23SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2PP2bs3LFB2kk6inext03sjh2S13Lc23SZCS1R5STKsi2LF2bs3LFB2kk6inext03sjh2S14prev3Lc23SZCS1R5STKsi2LF2PP2bs3LFB2kk6inext03sjh2S13Lc23SZCS1R5STKsi2LF2bs3LFB2kk6inext03sjh2S14prev3Lc23SZCS1R5STKsi2LF2bs3LFB2kk6inext03sjh2S14prev3Lc23SZCS1R5STKsi2LF2bs3LFB2kk6inext03sjh2S14prev3Lc23SZCS1R5STKsi2LF2bs3LFB2kk6inext03sjh2S14prev2Sn3Lc23SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2bs3LFB2kk6inext03sjh2S14prev2Sn3Lc23SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2bs3LFB2kk6inext03sjh2S14prev3Lc23SZC2HB5Ha_stS1R5STKsi2LF2bs3LFB2kk6inext03sjh2S14prev3Lc23SZC4PPOS2HBS1R5STKsi2LF2PP2bs3LFB2kk6inext03sjh2S13Lc23SZCFS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS2kk2FB3sp16inext03sjh2S14prev2Sn3Lc23SP14SP1M3SZC3PAL4PPOS2NP3ALO3ACV3SPR2F0S1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB3ALP3PP02kk2FB3sp16inext03sjh2S14prev2Sn3Lc23SZC2NP3SPR2F0S1R5STKsi2LF2bs3LFB2kk6inext03sjh2S14prev3Lc23SZC". (* [comment removed for export] *)
  #[using="IMG NS1 STKsi PHIsi_mono FFRsi_mono CNTsi_mono PHIsi_sadd FFRsi_sadd LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB SG0 CWS SGLO DSB DA0 CRDA DALO D1 D2 D3 SLOS SLOL SLO TOP SPH LOS"] Lemma LOOP_link : forall (kk : nat) (ES p p' cnt : Z) (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (s3v : word) (j32 : list byte)
      (inext0 : Z) (names0 : list Z) (sjh : signer_junk) (S1 : Z) (mid : list (Z * list Z)) (prev pinext : Z) (pnames : list Z) (psj : signer_junk)
      (Lc : list blk) (Sn inext2 : Z) (nodes2 : list Z) (sjn : signer_junk) mc moc hc
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    LOOPST kk ->
    ES - p' <= Z.of_nat kk -> P < p -> p < p' -> p' <= ES -> ES <= END -> 1 <= cnt -> cnt <= p - P ->
    gvA FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 (Z_to_bv 64 (-22400)) (Z_to_bv 64 SIG) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 DALG) j32 p' (signer_cells inext0 S1 sjh)
        (SNAME (rev nodes2) ++ (Sn, 200) :: Lc) mc moc hc ->
    OPENA mc Lc inext0 names0 S1 mid prev pinext pnames psj ->
    rw_cells asegs mc Sn (signer_cells inext2 0 sjn) ->
    name_chain asegs (fun _ => True) mc ((SNAME (rev nodes2) ++ (Sn, 200) :: Lc) ++ LB) inext2 nodes2 ->
    (forall x, In x nodes2 -> forall B k, In (B, k) (((Sn, 200) :: Lc) ++ LB) -> x + NAME_SIZE <= B \/ B + k <= x) ->
    Sn mod 16 = 0 -> 0 < Sn -> fresh_apart R LB LF Sn 200 ->
    (forall B k, In (B, k) (Lc ++ LB) -> Sn + 200 <= B \/ B + k <= Sn) ->
    SINV d (p' - P) (cnt + 1) PHIa FFRa (Z.of_nat (length (SNAME (rev nodes2) ++ (Sn, 200) :: Lc))) ->
    havol asegs R HIA h + PHIs PHIsi CNTsi NB <= AVOL_MAX -> hfr asegs R HIA h + FFRs FFRsi CNTsi NB d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 FB) s3v (Z_to_bv 64 cnt) (Z_to_bv 64 prev) (Z_to_bv 64 PP) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 Sn) (Z_to_bv 64 FB)
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 ES) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x98c3c) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until t6. intros K Hk Hp1 Hp2 Hp3 HES Hc1 Hc2 D OP CSn HNn HAPn NAL NP NFRn NAPc SI BUD BUDF UW.
    pose proof D as D0. gvA_open D. rt_facts. walk_prep. pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as Dnn.
    pose proof OP as OP0. ddestruct OP as (HN0 & HSP & PC & PN & PAL & PPOS & PIN & PVB & PNM & ELc & PFR).
    unfold SIGNER_SIZE in PIN, PVB.
    pose proof PFR as PF. ddestruct PF as (_ & PCE & _ & _).
    set (Lc2 := SNAME (rev nodes2) ++ (Sn, 200) :: Lc) in *.
    assert (SUB2 : forall b, In b (Lc ++ LB) -> In b (Lc2 ++ LB)).
    { intros b Hb. apply in_app_iff in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; subst Lc2; apply in_or_app; right; right; exact Hb| right; exact Hb]. }
    assert (PIN2 : In (prev, 200) (Lc2 ++ LB)) by (apply SUB2; apply in_or_app; left; exact PIN).
    assert (SIN2 : In (Sn, 200) (Lc2 ++ LB)) by (apply in_or_app; left; subst Lc2; apply in_or_app; right; left; reflexivity).
    pose proof (hm_aobj_block asegs R HIA hc _ _ mc prev 200 HHc PIN2) as OPV.
    pose proof (hm_aobj_block asegs R HIA hc _ _ mc Sn 200 HHc SIN2) as OSN.
    assert (NBp : p' - P <= NB) by (clear - Hp3 HES; lia).
    pose proof (CNTsi_mono 0 NB ltac:(clear - B1 B2; lia)) as CS0'. pose proof (PHIsi_mono 0 NB ltac:(clear - B1 B2; lia)) as PS0. pose proof (FFRsi_mono 0 NB (d + 1) ltac:(clear - B1 B2; lia)) as FS0.
    assert (CNT30 : cnt + 1 < 2^30) by (clear - Hc2 Hp2 Hp3 HES B1 B2 B3 B30; lia).
    pose proof (A_pkcs7_signers_C.sinv_bounds PHIsi FFRsi CNTsi PHIsi_mono FFRsi_mono CNTsi_mono PHIsi_sadd FFRsi_sadd d (p' - P) (cnt + 1) PHIa FFRa (Z.of_nat (length Lc2)) NB Dnn SI NBp) as (SB1 & SBU).
    destruct (SBU 0 ltac:(clear; lia) ltac:(clear - NBp; lia)) as (SB2 & SB3). clear SBU.
    pose proof (PHIsi_mono 0 0 ltac:(clear; lia)) as PSr. pose proof (FFRsi_mono 0 0 (d + 1) ltac:(clear; lia)) as FSr.
    (* [comment removed for export] *)
    destruct (hm_apart asegs R HIA hc _ _ _ HHc) as [_ BA].
    pose proof (blocks_apart_app2 _ _ (prev, 200) (FB, 64) BA PIN2 ltac:(left; reflexivity)) as APVF. cbn [fst snd] in APVF.
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 prev 200 PFR CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APVP.
    pose proof (frame_apart_obj R HIA LB LF lo _ SIG 200 prev 200 PFR CWS ltac:(clear; lia) ltac:(clear; lia) LOS) as APVS.
    pose proof (frame_apart_obj0 R HIA LB LF lo DALG 24 prev 200 PFR CRDA ltac:(clear; lia) ltac:(clear; lia) LOS) as APVD.
    pose proof (NAPc prev 200 ltac:(apply in_or_app; left; exact PIN)) as APVN.
    assert (NDJ : forall x k, In (x, k) (Lc2 ++ LB) -> (x, k) <> (prev, 200) -> 0 < k -> disjoint_from [(prev + 192, prev + 200)] x k).
    { intros x k Hx Hne Hkp. cbn [disjoint_from]. split; [| exact I].
      pose proof (blocks_apart_neq _ (x, k) (prev, 200) BA ltac:(apply in_or_app; left; exact Hx) ltac:(apply in_or_app; left; exact PIN2) Hne Hkp ltac:(cbn; clear; lia)) as X.
      cbn [fst snd] in X. clear - X. lia. }
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    match goal with |- context [Z_to_bv 64 (bv_swrap 32 ?e)] =>
      replace (Z_to_bv 64 (bv_swrap 32 e) : word) with (Z_to_bv 64 (cnt + 1) : word)
        by (apply bv_eq; first [change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear - Hc1; lia) | idtac];
            rewrite ?Z_to_bv_unsigned; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus;
            change (2 ^ Z.of_N 32) with 4294967296; change (4294967296 `div` 2) with 2147483648; change (2 ^ Z.of_N 64) with 18446744073709551616;
            clear - Hc1 CNT30; Z.div_mod_to_equations; lia)
    | |- ?g => idtac "LINK-ADDIW-FORM:" g end.
    (* [comment removed for export] *)
    unfold signer_cells in PC. cbn [sj0 sj_merged sj1 sj2] in PC.
    assert (SCSS : crange (hcs asegs R HIA hc) slo (bv_unsigned sp - slo)) by (eapply crange_sub; [exact SCS03c| clear - SLOS; lia| clear - SLOL SLO NS1 STKsi0 NRT TOP HT; lia]).
    pose proof (conj HHc (conj PRES (conj FHD (conj G4 (conj FSH (conj SAVE (conj RSL (conj PPc (conj CSG (conj DAc (conj BYc (conj CSn
                 (conj OPP (conj OSG (conj ODA (conj OBUF (conj SSc I))))))))))))))))) as CBOX.
    clear HHc PRES FHD G4 FSH SAVE RSL PPc CSG DAc BYc CSn OPP OSG ODA OBUF SSc OPPc OSGc ODAc OSN CSOK SB64.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => pose proof (munch_refl [(prev + 192, prev + 200)] mx) as MU3; pose proof (wmono_refl asegs mx) as WM3 end.
    step; zsimp.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m3 end.
    lazymatch type of MU3 with munch _ ?mx _ => rename mx into m2 end.
    ddestruct CBOX as (HH2 & PRES2 & FHD & G4 & FSH & SAVE & RSL & PPc & CSG & DAc & BYc & CSn & OPP & OSG & ODA & OBUF & SS2 & _).
    change (rw_cells asegs m3 prev (signer_cells pinext Sn psj)) in PC.
    pose proof (hcs_ok asegs R HIA hc) as CSOK2.
    assert (WCL : w_client (hcs asegs R HIA hc) [(prev + 192, prev + 200)]).
    { apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. eapply crange_sub; [exact (aobj_crange _ _ _ _ _ _ OPV)| clear; lia| clear; lia]. }
    assert (WLT : Forall (fun iv => fst iv < snd iv) [(prev + 192, prev + 200)]) by (apply Forall_cons; [cbn; clear; lia| apply Forall_nil]).
    assert (HH3 : HM asegs R HIA hc (Lc2 ++ LB) ((FB, 64) :: LF) m3).
    { eapply (hm_munch asegs R HIA hc); [exact HH2| exact MU3| exact WM3|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. left. right. right.
      exists (prev, 200). split; [apply in_or_app; left; exact PIN2| cbn [fst snd]; clear - Ha; lia]. }
    assert (PRES3 : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) X0 m m3).
    { eapply (presW_munch_cs R HIA) with (hq := hc); [exact PRES2| exact MU3| exact WM3| exact HCSc| exact WCL|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      eapply (wcover_fresh R LB LF _ X0 (prev + 192) _ prev 200 PFR); [clear; lia| clear; lia| clear - ALO LOS SLO NS1 STKsi0 NRT; lia]. }
    pose proof (rw_cells_transport asegs _ m2 m3 _ _ FHD MU3 WM3 ltac:(cbn [cells_size csize Nat.add length disjoint_from]; split; [clear - APVF; lia| exact I])) as FHD3.
    pose proof (rw_cells_transport asegs _ m2 m3 _ _ G4 MU3 WM3 ltac:(cbn [cells_size csize Nat.add length disjoint_from]; split; [clear - APVF; lia| exact I])) as G43.
    lazymatch type of FSH with rw_cells _ _ ?a ?cs =>
      assert (FSH3 : rw_cells asegs m3 a cs)
        by (eapply (shadow_cells_munch asegs AL (hcs asegs R HIA hc)); [exact CSOK2| exact WCL| exact WLT| cbn [cells_size csize Nat.add length Z.of_nat Z.mul Pos.mul Pos.of_succ_nat Pos.succ]; exact CFBc
                                                                    | clear - F0; lia| cbn; clear; lia| exact MU3| exact WM3| exact FSH]) end.
    pose proof (rw_cells_transport asegs _ m2 m3 _ _ SAVE MU3 WM3 ltac:(cbn [cells_size csize Nat.add length disjoint_from]; split; [clear - PCE ALO LOS SLO SP1 NS1 STKsi0 NRT; lia| exact I])) as SAVE3.
    pose proof (rw_cells_transport asegs _ m2 m3 _ _ RSL MU3 WM3 ltac:(cbn [cells_size csize Nat.add length disjoint_from]; split; [clear - PCE ALO LOS SLO SP1 NS1 STKsi0 NRT; lia| exact I])) as RSL3.
    pose proof (rw_cells_transport asegs _ m2 m3 _ _ PPc MU3 WM3 ltac:(cbn [cells_size csize Nat.add length disjoint_from]; split; [clear - APVP; lia| exact I])) as PPc3.
    pose proof (rw_cells_transport asegs _ m2 m3 _ _ CSG MU3 WM3 ltac:(rewrite SZC; cbn [disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ]; split; [clear - APVS; lia| exact I])) as CSG3.
    pose proof (rw_cells_transport asegs _ m2 m3 _ _ DAc MU3 WM3 ltac:(cbn [cells_size csize Nat.add length disjoint_from buf_cells]; split; [clear - APVD; lia| exact I])) as DAc3.
    pose proof (bytes_at_transport asegs _ m2 m3 _ _ BYc MU3 ltac:(cbn [disjoint_from]; split; [clear - PVB; lia| exact I])) as BYc3.
    pose proof (rw_cells_transport asegs _ m2 m3 _ _ CSn MU3 WM3 ltac:(cbn [cells_size csize Nat.add length disjoint_from signer_cells]; split; [clear - APVN; lia| exact I])) as CSn3.
    pose proof (aobj_back R CS _ m3 PP 8 (aobj_munch asegs AL _ CSOK2 _ m2 m3 PP 8 WCL MU3 (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OPP)) CRP) as OPP3.
    pose proof (aobj_back R CS _ m3 SIG 200 (aobj_munch asegs AL _ CSOK2 _ m2 m3 SIG 200 WCL MU3 (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OSG)) CRS) as OSG3.
    pose proof (aobj_back R CS _ m3 DALG 24 (aobj_munch asegs AL _ CSOK2 _ m2 m3 DALG 24 WCL MU3 (aobj_cs_mono asegs AL _ _ _ _ _ HCSc ODA)) CRDg) as ODA3.
    pose proof (aobj_back R CS _ m3 BUF n (aobj_munch asegs AL _ CSOK2 _ m2 m3 BUF n WCL MU3 (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBUF)) (aobj_crange _ _ _ _ _ _ OBUF)) as OBUF3.
    pose proof (sshad_munch asegs AL (hcs asegs R HIA hc) _ m2 m3 slo (bv_unsigned sp) CSOK2 WCL SCSS MU3 WM3 SS2) as SS3.
    pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OPP3) as OPP3c.
    (* [comment removed for export] *)
    assert (HPXb : heap_presx asegs L (Lc2 ++ LB) sp1 [(prev + 192, prev + 200)] m2 m3).
    { eapply heap_presx_of_munch; [exact MU3| exact WM3|]. intros a _ _ Ho. exact Ho. }
    assert (CHb : forall a' ns', name_chain asegs (fun _ => True) m2 (Lc2 ++ LB) a' ns' -> name_chain asegs (fun _ => True) m3 (Lc2 ++ LB) a' ns').
    { intros a' ns' HCx. eapply (chain_presx asegs L _ _ _ m2 m3 _ _ sp1 [(prev + 192, prev + 200)]);
        [exact HCx| intros x Hx; eapply (chain_nodes_in asegs); [exact HCx| exact Hx] | exact HPXb| unfold NAME_SIZE; clear; lia|].
      intros x Hx. apply NDJ; [eapply (chain_nodes_in asegs); [exact HCx| exact Hx] | unfold NAME_SIZE; intros E; apply (f_equal snd) in E; cbn in E; clear - E; lia| unfold NAME_SIZE; clear; lia]. }
    assert (HN03 : name_chain asegs (fun _ => True) m3 (Lc2 ++ LB) inext0 names0).
    { apply CHb. eapply chain_mem; [exact HN0| intros x Hx; apply SUB2; eapply (chain_nodes_in asegs); [exact HN0| exact Hx] | intros x cs _ HR _; exact HR]. }
    assert (PN3 : name_chain asegs (fun _ => True) m3 (Lc2 ++ LB) pinext pnames).
    { apply CHb. eapply chain_mem; [exact PN| intros x Hx; apply SUB2; eapply (chain_nodes_in asegs); [exact PN| exact Hx] | intros x cs _ HR _; exact HR]. }
    pose proof (CHb _ _ HNn) as HNn3.
    assert (HSP3 : splink asegs m3 (Lc2 ++ LB) S1 mid prev).
    { eapply splink_presx0; [| exact HPXb| |].
      - eapply splink_mem; [exact HSP| intros x _ Hx; apply SUB2; exact Hx| intros x cs _ _ HR _; exact HR|].
        intros i ns _ HN. eapply chain_mem; [exact HN| intros x Hx; apply SUB2; eapply (chain_nodes_in asegs); [exact HN| exact Hx] | intros x cs _ HR _; exact HR].
      - intros x Hx Hl. apply NDJ; [exact Hx| intros E; apply (f_equal fst) in E; cbn in E; subst x; exact (PNM Hl)| unfold SIGNER_SIZE; clear; lia].
      - intros i ns x _ HN Hx. apply NDJ; [eapply (chain_nodes_in asegs); [exact HN| exact Hx] | unfold NAME_SIZE; intros E; apply (f_equal snd) in E; cbn in E; clear - E; lia| unfold NAME_SIZE; clear; lia]. }
    assert (ELc2 : Lc2 = sbl ((mid ++ [(prev, pnames)]) ++ [(Sn, nodes2)]) ++ SNAME (rev names0)).
    { subst Lc2. rewrite ELc. rewrite (sbl_app (mid ++ [(prev, pnames)]) [(Sn, nodes2)]). cbn [sbl]. unfold SIGNER_SIZE. repeat rewrite <- app_assoc. reflexivity. }
    assert (OP3 : OPENA m3 Lc2 inext0 names0 S1 (mid ++ [(prev, pnames)]) Sn inext2 nodes2 sjn).
    { split; [exact HN03|]. split.
      { eapply splink_snoc; [exact HSP3| exact PIN2| exact PAL| exact PPOS| exact PC| exact PN3]. }
      split; [exact CSn3|]. split; [exact HNn3|]. split; [exact NAL|]. split; [exact NP|].
      split; [subst Lc2; apply in_or_app; right; left; reflexivity|].
      split; [exact (NAPc BUF n ltac:(apply in_or_app; right; exact BIN))|].
      split.
      { rewrite map_app. cbn [map fst]. intros Hin. apply in_app_or in Hin. destruct Hin as [Hin|[Hin|[]]].
        - assert (HL : In (Sn, 200) Lc) by (rewrite ELc; apply in_or_app; left; unfold SIGNER_SIZE in *; apply sbl_in_fst; rewrite map_app; apply in_or_app; left; exact Hin).
          pose proof (NAPc Sn 200 ltac:(apply in_or_app; left; exact HL)). clear - H. lia.
        - subst prev. clear - APVN. lia. }
      split; [exact ELc2| exact NFRn]. }
    clear HH2 PRES2 FHD G4 FSH SAVE RSL PPc CSG DAc BYc CSn OPP OSG ODA OBUF SS2 MU3 WM3 HPXb CHb HSP HN0 PN HNn OP0 D0 APVF APVP APVS APVD APVN NDJ WCL WLT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    assert (G3 : gvA FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 (Z_to_bv 64 (-22400)) (Z_to_bv 64 SIG) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 DALG) j32 p' (signer_cells inext0 S1 sjh) Lc2 m3 moc hc).
    { gvA_fin HKc MFc (mo_frame_refl moc). }
    assert (LEN2 : Z.of_nat (length Lc2) = Z.of_nat (length nodes2) + 1 + Z.of_nat (length Lc)).
    { subst Lc2. rewrite length_app. unfold SNAME. rewrite length_map, length_rev. cbn [length]. clear; lia. }
    (* [comment removed for export] *)
    zstep. if_cases KE; zify_cond KE;
      first [change 18446744073709551615 with (Z.ones 64) in KE; rewrite !Z.land_ones in KE by (clear - Hp1 Hp2 Hp3 HES B1 B2 B3 B47 B5; lia) | idtac];
      rewrite ?Z.mod_small in KE by (clear - Hp1 Hp2 Hp3 HES B1 B2 B3 B47 B5; lia).
    - (* [comment removed for export] *)
      intros moq [HKq MFq].
      eapply (K ES p' (cnt + 1)) with (mid := mid ++ [(prev, pnames)]) (prev := Sn) (pinext := inext2) (pnames := nodes2) (psj := sjn) (Lc := Lc2);
        first [ exact UW | exact BUD | exact BUDF | exact OP3 | exact HES | exact SI
              | eapply gvA_mo; [exact G3| exact HKq| exact MFq]
              | clear - KE Hk Hp1 Hp2 Hp3 HES Hc1 Hc2; lia
              | match goal with |- ?g => idtac "LINK-K-LEFT:" g end ].
    - (* [comment removed for export] *)
      zstep.
      intros moq [HKq MFq].
      eapply (ret_walk R HIA) with (STKsi := STKsi) (names0 := names0) (sg := (mid ++ [(prev, pnames)]) ++ [(Sn, nodes2)]) (inext := inext0) (snext := S1) (sj' := sjh)
                                   (PHIa := PHIa) (FFRa := FFRa) (slo := slo) (d := d) (lo := lo) (hc := hc) (mc := m3) (moc := moq) (Lc := Lc2) (W := X0) (r := cnt + 1);
        first [ sec_hyps
              | lazymatch goal with
                | |- name_chain _ _ _ _ _ _ => exact HN03
                | |- signer_chain _ _ _ _ _ => exact (CLOSEA R LB LF BUF bs _ _ _ _ _ _ _ _ _ _ OP3)
                | |- Permutation _ _ => rewrite ELc2; apply PERMc
                | |- Z.of_nat (length Lc2) <= _ => clear - SB1; lia
                | |- PHIa <= _ => unfold AVOL_CALL in *; clear - SB2 PSr; lia
                | |- FFRa <= _ => assert (L3 : 0 <= (A_pkcs7_signers_C.CNTs CNTsi NB + 1) * fr_charge (d + 1)) by (unfold fr_charge; clear - SB1 Dnn; nia);
                    unfold fr_charge in *; clear - SB3 FSr Dnn L3; lia
                | |- forall x, outside _ x -> outside _ x => intros x Hx; exact Hx
                | |- _ < cnt + 1 < _ => clear - Hc1 CNT30; lia
                end
              | eapply gvA_mo; [exact G3| exact HKq| exact MFq]
              | match goal with |- ?g => idtac "LINK-RET-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00c0@L10717529320.2  L12215599913.15 L12447271209.10 L14521127117.3  L14916060331.3  L15756354262.7  L16596701601.0  L18724180114.6  L18938185144.287L21111704458.7  L24381013773.18 L24499978319.4  L26081253460.3  L27111942217.1  L29010569984.275L31424281529.10 L31426805549.11 L32759717734.18 L33372728484.4  L34248762814.15 L35047717312.11 L35666023782.12 L37653189664.9  L38308634325.0  L39011098369.15 L39126682446.15 L39194698833.6  L39332637397.0  L40228640085.0  L40423050330.3  L41302442785.0  L42927756920.1  L43573326143.15 L43870962401.3  L45174269619.15 L4546204532.4   L49493397620.5  L50457964827.5  L52852529520.4  L57282768967.14 L58971104604.2  L59308633593.3  L59310684369.4  L60098763854.6  L62252464380.9  L6314234736.15  L66151426447.10 L67616200298.12 L7591358181.13  Q21913096607.296Q7526558210.296 00000700J01201:01D01R01S01g04@04P05705H05Q05U05V06<06h07N07[08008^09:09]09^0:30:i0;@0;A0;B0;L0;M0;R0;f0<00<B0<L0<V0<j0=40=l0>70>A0>N0>X0?70?M0?]0@J0A<0BX0D0S1d3DnnS2kk2ES1p2Hk2p'3Hp'S5PHIsi5CNTsi1P3END2ES1p4PHIa2Lc3SB23PSrS1P1p2p'S2ES1p3Hp2S1R2lo3LOS3ALOSS1P3END2ES1p3Hp23HESS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS2kk2ES1p2FB3sp16inext06names03sjh2S13mid4prev6pnames2Lc2Hk4PPOS3ALO3ACV3SPR2Sn2NP3NCE3SP13SZC2F0S1P3END2ES1p3HESS1R3HIA5STKsi1h2sp3SIG2lo4SGLO3SLO1q2HqS5PHIsi1P3END3PS0S1p2p'2U4S2PPFS1R3HIA5PHIsi1h2ES1p4PHIa2Lc3PSr5ROOMVS1R3HIA5PHIsi1h2ES1p4PHIa2Lc5ROOMV4PHIx4HPXBS1R3HIA5STKsi1h2sp2PP2lo4PPLO3SLO1q2HqS1P3END1p3NBpS2kk2ES1p2Hk2p'5HprogS5PHIsi5CNTsi1P3END2ES1p4PHIa2Lc3SB24PHIx4HPXBS1R3HIA5STKsi1h2sp2lo3TOP2HTS1R3HIA5PHIsi1h2ES1p4PHIa3PSr5ROOMVSS2kk2ES1p2Hk2p'5HprogS1R3HIA5FFRsi5CNTsi1h1P3END1d2ES1p4FFRa2Lc4BUDF3SB32LKS5FFRsi1P3END1d3Dnn3FS0SSS2ES1p3Hp2SS3SIGS2kk2ES1p3cnt2Hk3Hc1S2ES1p3Hp2S1P2kk2ES1p2Hk3Hp1S2Sn1x1k1XS1P3END2B2S5CNTsi1P3END2Lc3SB1S2PP1x1k1XS5FFRsi5CNTsi1P3END1d2ES1p4FFRa2Lc3SB34FRC02LK4FFRx4HFXBS2Lc6nodes2S2Sn2NP2KZS2ES1p2Hk3Hp2S1R2lo3LOSS1R3HIA5PHIsi1h2ES1p4PHIa5ROOMVS1P2kk2ES1p3cnt2Hk3Hc2S1r2Hr2r02KR1q1HS1R3HIA5PHIsi5CNTsi1h1P3END2ES1p4PHIa3BUD3SB2S5FFRsi5CNTsi1P3END1d2ES1p4FFRa2Lc3SB33FSr4FRC02LKS1R5STKsi2LF2sp2lo2bs3LFB3SLO2kk2ES1p3sp16inext06names03sjh2S13mid4prev6pnames2Lc2Hk3SP13SZCS1R5STKsi2LF2sp2lo2bs3LFB2kk2ES1p3sp16inext06names03sjh2S13mid4prev6pnames2Lc2Hk3SP13SZC". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND CALLOC FREE STKsi SIGNER PHIsi_mono FFRsi_mono CNTsi_mono PHIsi_sadd FFRsi_sadd CNTsi_sadd LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALS SG0 CWS SGLO DSB ALD DA0 CRDA DALO Q1 Q2 Q3 D1 D2 D3 SLOS SLOL SLO TOP SPA SPH TPV LOS"] Lemma LOOP : forall kk, LOOPST kk.
  Proof.
    induction kk as [|kk IH]; unfold LOOPST; intros ES p cnt FB sp1 PHIa FFRa w0 w1 w2 lw b4 s3v j32 inext0 names0 sjh S1 mid prev pinext pnames psj Lc mc moc hc
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s8v Hk Hp1 Hp2 HES Hc1 Hc2 D OP SI BUD BUDF UW; [exfalso; clear - Hk Hp2; lia|].
    pose proof D as D0. gvA_open D. rt_facts. walk_prep. pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as Dnn.
    pose proof OP as OP0. ddestruct OP as (HN0 & HSP & PC & PN & PAL & PPOS & PIN & PVB & PNM & ELc & PFR).
    unfold SIGNER_SIZE in PIN, PVB.
    pose proof (CNTsi_mono 0 NB ltac:(clear - B1 B2; lia)) as CS0'. pose proof (PHIsi_mono 0 NB ltac:(clear - B1 B2; lia)) as PS0. pose proof (FFRsi_mono 0 NB (d + 1) ltac:(clear - B1 B2; lia)) as FS0.
    assert (NBp : p - P <= NB - 1) by (clear - Hp2 HES; lia).
    pose proof (lenLc _ _ _ ELc) as EL.
    (* [comment removed for export] *)
    assert (CIT0 : 0 <= CIT) by (unfold AVOL_CALL; clear - PS0; lia).
    assert (FIT0 : 0 <= FIT) by (unfold fr_charge; clear - FS0 Dnn; lia).
    pose proof (A_pkcs7_signers_C.sinv_bounds PHIsi FFRsi CNTsi PHIsi_mono FFRsi_mono CNTsi_mono PHIsi_sadd FFRsi_sadd d (p - P) cnt PHIa FFRa (Z.of_nat (length Lc)) NB Dnn SI ltac:(clear - NBp; lia)) as (SB1 & SBU).
    destruct (SBU (ES - p) ltac:(clear - Hp2; lia) ltac:(clear - Hp2 HES Hp1; lia)) as (SB2 & SB3). clear SBU.
    pose proof (PHIsi_mono (ES - p) (ES - p) ltac:(clear - Hp2; lia)) as PSr. pose proof (FFRsi_mono (ES - p) (ES - p) (d + 1) ltac:(clear - Hp2; lia)) as FSr.
    assert (FRC0 : 0 <= fr_charge (d + 1)) by (unfold fr_charge; clear - Dnn; lia).
    assert (LK : (Z.of_nat (length Lc) + 1) * fr_charge (d + 1) <= (A_pkcs7_signers_C.CNTs CNTsi NB + 1) * fr_charge (d + 1)) by (apply Z.mul_le_mono_nonneg_r; [exact FRC0| clear - SB1; lia]).
    assert (ROOMV : havol asegs R HIA h + PHIa + (PHIsi (ES - p) + 2 * 200 + 2 * AVOL_CALL) <= AVOL_MAX) by (unfold AVOL_CALL in *; clear - BUD SB2; lia).
    assert (ROOMF : hfr asegs R HIA h + FFRa + (FFRsi (ES - p) (d + 1) + 2 * fr_charge (d + 1)) + (Z.of_nat (length Lc) + 1) * fr_charge (d + 1) <= FR_MAX) by (clear - BUDF SB3 LK; lia).
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    assert (TST1 : forall q, bv_unsigned sp <= q < hstkhi asegs R HIA h -> outside X0 q).
    { intros q Hq. cbn [outside]. split; [clear - Hq PPLO LOS SLO NS1 STKsi0 NRT; lia| split; [clear - Hq SGLO LOS SLO NS1 STKsi0 NRT; lia| exact I]]. }
    eapply (calloc_stepA R HIA) with (STKsi := STKsi) (hc := hc) (moc := moc) (mc := mc) (Lc := Lc) (PHIa := PHIa) (FFRa := FFRa) (slo := slo) (d := d) (W := X0) (lo := lo);
      first [ exact D0 | exact UW | exact TST1 | sec_hyps
            | lazymatch goal with
              | |- havol _ _ _ _ + _ + _ <= _ => unfold AVOL_CALL in *; first [clear - ROOMV HPXB; lia | clear - ROOMV PSr; lia]
              | |- hfr _ _ _ _ + _ + _ <= _ => first [clear - ROOMF HFXB FRC0; nia | clear - ROOMF FSr FRC0; nia]
              | |- 0 <= _ < 2 ^ 64 => clear; lia
              | |- _ mod 2 = 0 => reflexivity
              | |- forall m1 mo1 h1, _ => idtac
              end
            | match goal with |- ?g => idtac "LOOP-CALLOC-LEFT:" g end ].
    { (* [comment removed for export] *)
      cbv beta. intros m1 mo1 h1 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 G1 HPc.
      assert (OP1 : OPENA m1 Lc inext0 names0 S1 mid prev pinext pnames psj).
      { eapply (OPENA_presx R LB LF BUF bs mc m1 Lc); [exact OP0| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HPc)| intros b Hb; apply in_or_app; left; exact Hb| intros; exact I]. }
      intros moq [HKq MFq].
      eapply (LOOP_cfail R HIA) with (STKsi := STKsi) (PHIa := PHIa + (2 * 200 + AVOL_CALL)) (FFRa := FFRa + fr_charge (d + 1)) (slo := slo) (d := d) (lo := lo)
                                      (hc := h1) (mc := m1) (moc := moq) (Lc := Lc);
        first [ exact UW | exact (proj1 OP1) | exact (CLOSEA R LB LF BUF bs _ _ _ _ _ _ _ _ _ _ OP1) | exact ELc | sec_hyps
              | lazymatch goal with
                | |- havol _ _ _ _ + _ + _ <= _ => unfold AVOL_CALL in *; first [clear - ROOMV HPXB; lia | clear - ROOMV PSr; lia]
                | |- hfr _ _ _ _ + _ + _ <= _ => first [clear - ROOMF HFXB FRC0; nia | clear - ROOMF FSr FRC0; nia]
                | |- _ + _ * AVOL_CALL <= A_pkcs7_signers_C.PHIs _ _ _ => unfold AVOL_CALL in *; first [clear - SB2 HPXB; lia | clear - SB2 PSr; lia]
                | |- _ + _ * fr_charge _ <= A_pkcs7_signers_C.FFRs _ _ _ _ => first [clear - SB3 LK HFXB FRC0; lia | clear - SB3 LK FSr FRC0; lia]
                end
              | eapply gvA_mo; [exact G1| exact HKq| exact MFq]
              | match goal with |- ?g => idtac "LOOP-CFAIL-LEFT:" g end ]. }
    (* [comment removed for export] *)
    cbv beta. intros m1 mo1 h1 Sn y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 G1 CSn NAL NP NCE NFR NFR2 HPc.
    assert (OP1 : OPENA m1 Lc inext0 names0 S1 mid prev pinext pnames psj).
    { eapply (OPENA_presx R LB LF BUF bs mc m1 Lc); [exact OP0| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HPc)| intros b Hb; apply in_or_app; left; exact Hb| intros; exact I]. }
    assert (NAPc : forall B k, In (B, k) (Lc ++ LB) -> Sn + 200 <= B \/ B + k <= Sn).
    { intros B k Hb. ddestruct NFR2 as (_ & _ & _ & F3'). apply F3'. apply in_or_app. left. exact Hb. }
    pose proof G1 as G1'. ddestruct G1' as (HH1 & HK1 & MF1 & HT1 & HS1 & HF1 & HCS1 & _).
    assert (APc1 : forall x k, In (x, k) Lc -> 0 < k -> x + k <= PP \/ PP + 8 <= x).
    { intros x k Hx Hkp. eapply (obj_apart_new R HIA h1 ((Sn, 200) :: Lc) LB LF ((FB, 64) :: LF) m1 lo _ PP 8 x k);
        [exact DIMG| exact HH1| intros fb Hfb; right; exact Hfb| exact CWP| clear - ALO LOS; lia| clear; lia| right; exact Hx| exact Hkp]. }
    clear HHc HKc MFc HTc HSc HFc HCSc HVc HFRc PRES SP1 SP1M F64 FRSH CFB FHD G4 FSH SAVE RSL STb STlo PPc Hpc CSG SZC DAc BYc OPP OSG ODA OBUF MIc SSc LAWS KINV HPc.
    clear CSOKc HT CFBc SCS03c SCS SCSc OPPc OSGc ODAc CRP CRS CRDg APP APSG F0 F1 F2 F3 STKH WL WCS WCP CWSc CWPc.
    pose proof G1 as G1'. gvA_open G1'. walk_prep.
    pose proof (AIh_laws asegs R HIA h1) as LAWS. pose proof (KF_kinv asegs R HIA h1 mo1) as KINV.
    (* [comment removed for export] *)
    zstep. if_cases KZ; zify_cond KZ; [exfalso; kz2 KZ NP NCE; clear - KZ NP; lia|].
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply (signer_step_node R HIA) with (STKsi := STKsi) (hc := h1) (moc := mo1) (mc := m1) (Lc := (Sn, 200) :: Lc) (S := Sn) (sjs := sjZ) (ENDx := ES)
                                          (PHIa := PHIa + (2 * 200 + AVOL_CALL)) (FFRa := FFRa + fr_charge (d + 1)) (slo := slo) (d := d) (lo := lo) (p := p)
                                          (sgc := signer_cells inext0 S1 sjh) (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0)
                                          (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
      first [ exact G1 | exact UW | exact CSn | exact NAL | exact NP | exact NFR | exact HES | sec_hyps
            | lazymatch goal with
              | |- In (Sn, 200) _ => left; reflexivity
              | |- p <= ES => clear - Hp2; lia
              | |- havol _ _ _ _ + _ + _ <= _ => unfold AVOL_CALL in *; first [clear - ROOMV HPXB; lia | clear - ROOMV PSr; lia]
              | |- hfr _ _ _ _ + _ + _ <= _ => first [clear - ROOMF HFXB FRC0; nia | clear - ROOMF FSr FRC0; nia]
              | |- 0 <= _ < 2 ^ 64 => clear; lia
              | |- _ mod 2 = 0 => reflexivity
              | |- forall m2 mo2 h2, _ => idtac
              end
            | match goal with |- ?g => idtac "LOOP-SIGNER-LEFT:" g end ].
    cbv beta. intros m2 mo2 h2 r p' inext2 sjn nodes2 PHIx FFRx z0 z1 z2 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 G2 CS2 Hr Hp' Hprog Hnodes HNC2 HND2 HAP2 HCNT2 HPXB HFXB HSUC HPX2.
    assert (OP2 : OPENA m2 Lc inext0 names0 S1 mid prev pinext pnames psj).
    { eapply (OPENA_presx R LB LF BUF bs m1 m2 Lc); [exact OP1| exact HPX2| |].
      - intros b Hb. apply in_or_app. left. cbn [app]. right. exact Hb.
      - intros x k Hx Hkp. cbn [disjoint_from]. split; [pose proof (APc1 x k Hx Hkp) as X; clear - X; lia|].
        split; [pose proof (NAPc x k ltac:(apply in_or_app; left; exact Hx)) as X; clear - X; lia| exact I]. }
    clear HHc HKc MFc HTc HSc HFc HCSc HVc HFRc PRES SP1 SP1M F64 FRSH CFB FHD G4 FSH SAVE RSL STb STlo PPc Hpc CSG SZC DAc BYc OPP OSG ODA OBUF MIc SSc LAWS KINV.
    clear CSOKc HT CFBc SCS03c SCS SCSc OPPc OSGc ODAc CRP CRS CRDg APP APSG F0 F1 F2 F3 STKH WL WCS WCP CWSc CWPc.
    pose proof G2 as G2'. ddestruct G2' as (HH2 & HK2 & MF2 & _).
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo2) as KINV.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      assert (RNZ : r <> 0) by (intros E; rewrite E in KR; cbv in KR; first [exact (KR eq_refl) | congruence | lia]).
      specialize (Hnodes RNZ). subst nodes2. cbn [rev SNAME map app] in G2.
      intros moq [HKq MFq].
      eapply (LOOP_sfail R HIA) with (STKsi := STKsi) (PHIa := PHIa + (2 * 200 + AVOL_CALL) + PHIx) (FFRa := FFRa + fr_charge (d + 1) + FFRx)
                                      (slo := slo) (d := d) (lo := lo) (hc := h2) (mc := m2) (moc := moq) (Lc := Lc) (Sn := Sn) (r := r);
        first [ exact UW | exact (proj1 OP2) | exact (CLOSEA R LB LF BUF bs _ _ _ _ _ _ _ _ _ _ OP2) | exact ELc | exact Hr | exact RNZ | sec_hyps
              | lazymatch goal with
                | |- havol _ _ _ _ + _ + _ <= _ => unfold AVOL_CALL in *; first [clear - ROOMV HPXB; lia | clear - ROOMV PSr; lia]
                | |- hfr _ _ _ _ + _ + _ <= _ => first [clear - ROOMF HFXB FRC0; nia | clear - ROOMF FSr FRC0; nia]
                | |- _ + _ * AVOL_CALL <= A_pkcs7_signers_C.PHIs _ _ _ => unfold AVOL_CALL in *; first [clear - SB2 HPXB; lia | clear - SB2 PSr; lia]
                | |- _ + _ * fr_charge _ <= A_pkcs7_signers_C.FFRs _ _ _ _ => first [clear - SB3 LK HFXB FRC0; lia | clear - SB3 LK FSr FRC0; lia]
                end
              | eapply gvA_mo; [exact G2| exact HKq| exact MFq]
              | match goal with |- ?g => idtac "LOOP-SFAIL-LEFT:" g end ].
    - (* [comment removed for export] *)
      assert (R0 : r = 0).
      { first [change 18446744073709551615 with (Z.ones 64) in KR; rewrite ?Z.land_ones in KR by (clear; lia) | idtac]. clear - KR Hr. Z.div_mod_to_equations. lia. }
      subst r. specialize (Hprog eq_refl).
      assert (LEN2 : Z.of_nat (length (SNAME (rev nodes2) ++ (Sn, 200) :: Lc)) = Z.of_nat (length nodes2) + 1 + Z.of_nat (length Lc)).
      { rewrite length_app. unfold SNAME. rewrite length_map, length_rev. cbn [length]. clear; lia. }
      zpre.
      intros moq [HKq MFq].
      eapply (LOOP_link kk ES p p' cnt) with (PHIa := PHIa + (2 * 200 + AVOL_CALL) + PHIx) (FFRa := FFRa + fr_charge (d + 1) + FFRx)
                                              (hc := h2) (mc := m2) (moc := moq) (Lc := Lc) (Sn := Sn) (prev := prev) (mid := mid);
        first [ exact IH | exact UW | exact OP2 | exact CS2 | exact HNC2 | exact HND2 | exact HAP2 | exact NAL | exact NP | exact NFR | exact NAPc | exact HES | exact BUD | exact BUDF
              | eapply gvA_mo; [exact G2| exact HKq| exact MFq]
              | lazymatch goal with
                | |- A_pkcs7_signers_C.SINV _ _ _ _ _ _ _ _ _ =>
                    rewrite LEN2; replace (p' - P) with ((p - P) + (p' - p)) by (clear; lia); ddestruct (HSUC eq_refl) as (U1 & U2 & U3 & U4);
                    eapply (A_pkcs7_signers_C.sinv_step PHIsi FFRsi CNTsi PHIsi_sadd FFRsi_sadd CNTsi_sadd); [exact Dnn| exact SI| clear - U4; lia| exact U1| exact U2| exact U3]
                | |- _ => clear - Hk Hp1 Hp2 HES Hc1 Hc2 Hp' Hprog; lia
                end
              | match goal with |- ?g => idtac "LOOP-LINK-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
