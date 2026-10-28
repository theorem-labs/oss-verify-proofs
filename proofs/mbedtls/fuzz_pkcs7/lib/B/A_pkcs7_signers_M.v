(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_pkcs7_signers.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag
     A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt A_pkcs7_signers_A A_pkcs7_signers_B A_pkcs7_signers_C A_pkcs7_signers_D A_pkcs7_signers_E A_pkcs7_signers_F A_pkcs7_signers_G A_pkcs7_signers_H A_pkcs7_signers_I A_pkcs7_signers_J A_pkcs7_signers_K A_pkcs7_signers_L.
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
Local Ltac zchk_fails ::= constr:([0x98e24]).
Local Ltac zchk_new ::= constr:([0x98a4c; 0x98b3c; 0x98b90; 0x98b94; 0x98b98; 0x98ba4; 0x98bb8; 0x98bbc; 0x98bc0; 0x98bc4; 0x98bd0; 0x98be0; 0x98c34; 0x98c38; 0x98c50; 0x98c58; 0x98c5c; 0x98c6c; 0x98ce8; 0x98cf0; 0x98cf4; 0x98d08; 0x98d0c; 0x98d2c; 0x98d30; 0x98d88; 0x98d8c; 0x98dc4; 0x98dc8]).
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



  Local Notation S1P := (S1P R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP P END BUF SIG DALG lo slo bs dtg dpad dlen dq sj).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04;0@C40858145355.260C60410007123.259D10636937134.260D16071854214.260D2457516971.260 D25900232977.302D32458870384.260D39565106411.261D46794843979.260D60109446735.260D60189065437.261D60189065437.302D65008160014.260D68221095944.260K14960815226.260K20981739667.258K29378133114.260K30993319891.260K48171199513.260K4855522682.260 K53642109465.260K65858155712.259L10717529320.2  L11431517604.18 L12126572370.2  L12145010328.6  L12790317110.3  L12790320428.4  L14258790103.5  L14695814100.3  L14956783596.2  L15479883060.4  L16720171459.283L16809010849.0  L1685717371.0   L18457785511.0  L20009830093.12 L20977711877.2  L21654730866.2  L22376153118.6  L25215554980.11 L2536597402.3   L2621559066.1   L26343049312.6  L26892418956.1  L27111942217.1  L27666008530.2  L27832436220.235L27940405558.10 L28316294259.17 L28632618922.2  L28697523208.14 L29010569984.285L29391009772.3  L30507144274.2  L30997223346.3  L34254339088.2  L35666023782.12 L37232046390.2  L38072332913.3  L38235734261.1  L38259954321.2  L38308634325.0  L38691415991.0  L39076636629.0  L39172636981.0  L39280637297.0  L39332637397.0  L40228640085.0  L40281191306.3  L41202929119.244L41202929119.283L41251426164.1  L42488948659.2  L42609104409.283L42927756920.1  L43317676572.3  L44166924249.3  L44581594791.7  L44921588402.0  L45623375226.4  L46861370584.243L47870616696.2  L48171524228.2  L4859948780.3   L49233373885.2  L49493397620.5  L5021251703.1   L50678314462.3  L50790731766.12 L50963413453.2  L52753581537.3  L52895316838.2  L53154958140.5  L53617080676.3  L53642658618.9  L53646818791.3  L55281759534.4  L57387013391.2  L576250137.242  L57698627611.2  L58972524609.3  L59090792514.3  L59308586248.2  L59427880762.243L60098763854.6  L60812373952.12 L60948408515.6  L62275882349.3  L62560708162.2  L64179129035.1  L64584259670.9  L64630569949.3  L64962779489.3  L65110679799.3  L65862516566.2  L66151426447.10 L66151427842.16 L66298372189.2  L66572605252.10 L66812728480.3  L67070089790.2  L67653551064.2  L67922604617.0  L68410782481.4  L8060680993.0   L881835912.0    L9080220944.4   L9356559676.17  O11960516644.260O14568686558.257O14912726833.259O18988691132.259O20866770946.260O22525005962.259O25522832421.260O30010457231.259O31364011300.260O3493317847.258 O37559489567.260O3821773283.260 O424351700.258  O44938202843.258O45108703401.257O49701823576.259O50011839873.258O52099334849.260O55209884805.258O64474006218.259O66321155265.260O7474055973.260 P12115299733.261P12115299733.302P12795822833.261P12795822833.302P28627113325.261P28627113325.302P30511339222.259P37243319281.261P37243319281.302P38078079190.257P38261788758.261P38261788758.302P42484919333.259P44164039966.261P44164039966.302P47876372191.258P49230739482.259P50671478649.258P53607099331.257P57713046236.261P57713046236.302P59105944293.260P62260666314.258P62545491173.260P66292560634.259P66818508295.260P67064334489.259Q10592533181.260Q10598576460.235Q10598692432.255Q10636937134.260Q10637019692.296Q10649498890.258Q10649498890.297Q10651814432.257Q11133374175.260Q11657053839.260Q13730992401.296Q13733171485.257Q17027695041.260Q17681074618.260Q17701933584.258Q17701933584.297Q19561597574.235Q21767670690.260Q21845213585.260Q21914785289.257Q23219026840.260Q27458512306.261Q27458512306.302Q27573751300.260Q27940818463.257Q27942454161.260Q27942899219.296Q2803826605.260 Q28465177121.258Q28465177121.299Q29775981542.260Q32681607669.260Q32681824661.261Q32681824661.302Q33137450695.260Q33947563126.298Q3419689062.261 Q3419689062.302 Q3421936230.260 Q3421936230.301 Q35288190350.296Q35294465410.257Q37149073081.261Q37149073081.302Q38167875878.261Q38167875878.302Q39180574961.261Q39180574961.302Q39600066516.258Q40249520655.235Q42439168719.260Q42439443119.261Q42439443119.302Q45353704351.257Q45360044947.296Q46794843979.260Q48118064779.260Q50294066241.255Q5265442331.259 Q5265442331.300 Q53380958617.258Q53380958617.297Q55415036769.261Q55415036769.302Q56530976407.260Q56854244147.261Q56854244147.302Q57228775306.260Q57228775306.301Q57230951818.261Q57230951818.302Q59321350679.302Q59865321072.261Q59865321072.302Q59865603600.260Q60071281945.258Q60071281945.297Q61847600945.258Q61847600945.297Q61957894121.260Q63766355947.298Q64683667846.261Q64683667846.302Q64683942374.260Q6771375012.260 Q7528279444.257 Q9356756743.237 Q9633850233.235 Q9644583048.260 00000400800h02?02@04904i06U07E08<09b0;U0<E0=b0?00@90AF0Ak0BP0C^0DB0EK0ER0F@0FA0F^0F_0F`0G10G;0G<0GK0IW0IX0IY0IZ0JL0JM0JN0Je0KN0KX0K]0Kl0L00L40L<0Ll0MG0N00N10Nf0Ng0Nh0Ni0Nj0Nk0OG0OH0OI0OM0ON0OO0OP0OQ0OR0OS0OT0OU0O^0PN0QK0QO0QP0SU0SZ0Se0Sf0T;0T<0TM0Ue0Uf0Ug0Uh0Ui0V30V40V50VP0VX0Vb0Vh0W90W:0Wa0Wb0X30X:0Xj0Xk0Y70Y80Y>0Y?0YI0Yl0ZH0ZI0ZJ0ZK0[20[;0[E0[O0[P0[`0\C0\D0\U0\V0\W0\_0\`0\o0]00]10]@0]k0]l0]m0]n0]o0^00^10^20^30^40^50^60^70^80^90^:0^;0^<0^=0^X0^Y0^Z0^[0_g0a70b@0cQ0dc0f90fe0gn0i@0j>0kP0lf0m\0o010H11B12<12e13]14Z15[16P17?18518Z19V1:J1:g1;D1;a1<>1<h1=E1=o1>L1>i1>j1?T1@11@N1AB1A_1BI1CU1DI1DJ1E61ES1F\1Gm1Gn1HZ1IF1J?1J]1KC1L61L[1L\1L]1L^1MF1N?1O?1PC1QC1RG1S<1Sd1U01V@1VA1VB1WN1X^1X_1Y<1Y_1Z^1[a1\>1\h1]E1^11^N1_51_i1_j1_k1`h1ai1aj1ak1al1c01d81e<1fD1fE1fF1fG1fH1fI1fJ1gN1h_1iT1jI1kS1la1mO1mP1n81n[1o;1o[S2PPS2FBS1R5STKsi2LF2sp2PP3SIG4DALG2bs2sj3LFB2FB3sp13SZCS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs2sj3LFB3PP03SG03DA03SLO3LOS2FB3sp13SP13SZC3SPR2F04SP1RFS1R3HIA5STKsi1h2LF2sp2PP3SIG4DALG2bs3LFB3PP03SG03DA03TOP2FB3sp13SPR4SP1R2h35inext3sj'5nodes3HTc3SP13SZC2F02HB5Ha_st5Hl_stS1R5STKsi2LF2sp2PP3SIG4DALG2bs2sj3LFB2FB3sp13SZCS1R3HIA5STKsi1h2LF2sp2PP3SIG4DALG2bs2sj3LFB3PP03SG03DA03TOP2FB3sp12h13HTc3SP13SZC3SPR2F04SP1R2HB5Ha_st5Hl_stS1R5STKsi2LF2sp2PP3SIG4DALG2bs2sj3LFB2FB3sp13SZCS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs2sj3LFB3LOS2FB3sp13SZCS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs2sj3LFB3PP03SG03DA03SLO3LOS2FB3sp13SP13SZC3SPR2F04SP1R2HB5Ha_st5Hl_stS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS2FB3sp13SPR4SP1R5inext3sj'5nodes3SP13SZC2F02HB5Ha_st5Hl_stS1R5STKsi2LF2sp2PP3SIG4DALG2bs2sj3LFB2FB3sp13SZCS1R3HIA5STKsi1h2LF2sp2PP3SIG4DALG2bs2sj3LFB3PP03SG03DA03TOP2FB3sp12h13HTc3SP13SZC3SPR2F04SP1RS1R5STKsi2LF2PP1P3END4DALG2lo2bs2sj3LFB2FB3sp13x153SZC3APD2x33x163x173x184POSTS1R5STKsi2LF2PP1P3END2lo2bs2sj3LFB2FB3sp13x153SZC3APP2x33x163x173x184POSTS1R5STKsi2LF2PP1P3END3BUF2lo2bs2sj3LFB2FB3sp13x153SZC3APB2x33x163x173x184POSTS1R5STKsi2LF2PP3BUF2bs2sj3LFB3DPB3SZCS1R5STKsi2LF2PP4DALG2bs2sj3LFB2D23SZCS1R5STKsi2LF2PP1P3END3SIG2lo2bs2sj3LFB2FB3sp13x153SZC4APSG2x33x163x173x184POSTS1R5STKsi2LF2PP3SIG2bs2sj3LFB2D13SZCS1R5STKsi2LF2PP1P3END2lo2bs2sj3LFB2FB3sp13x153SZC3APP2x33x163x173x184POSTS1d3DnnS1R5STKsi2sp3BUF2lo2bs3SLO3LOS3sp13SP13ALO3BCEFS5CNTsi1P3END3SZ55nodes5HCNT3FFS2p12Lw2p'3Hp'2KES2p12Lw2LRFS3BUF2bs2FB3APBS1R5STKsi2LF2sp2PP1P3END3BUF3SIG4DALG2bs3LFB3PP02B12B32B53SG03DA02FB3sp13ACV3SPR4SP1R3BCE2p12Lw4Hp1a3HLw2p'5inext3sj'5nodes3Hp'5Hprog3SZC2F0SSSS5FFRsi5CNTsi1P3END1d4FRC03SZ42p12Lw3SY34FFRx4HFXBFFS1P3END2p13Hp12p'5HprogS1R3HIA5PHIsi5CNTsi1h1P3END3BUD2p12Lw3SY2S2p12Lw2LRS3sp1S3END2p12Lw3HLwS2spS2PPS2r13Hr1S1R5STKsi2LF2sp2PP3SIG4DALG2bs2sj3LFB2FB3sp13SZCS1R5STKsi2sp2lo3SLO3sp13SP1S1R5STKsi2sp2lo3SLO3LOS2FB3sp13SP13ALO2F1FS1R3HIA5FFRsi5CNTsi1h1P3END1d4BUDF4FRC03SZ42p12Lw3SY3FFFFSS1R3HIA5STKsi1h2sp2lo3TOP2HTFFS2loFSSSSSSSS1R3HIA1hS1R5STKsi2LF2sp2PP3SIG4DALG2bs2sj3LFB2FB3sp13SZCS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp15inext3sj'5nodes3SZCS2FBFS1R5STKsi2LF2sp2PP1P3END3BUF3SIG4DALG2bs3LFB3PP02B12B32B53SG03DA02FB3sp13ACV3SPR4SP1R3BCE2p14Hp1a2p'5inext3sj'5nodes5Hprog3Hpc3SZC2F0S3SIGS2PP2FB3APPFS1P3END2p12Lw3Hp13HLwSS5CNTsi1P3END3SZ1S1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs2sj3LFB3PP04PPLO3SG03DA03SLO3SPH2FB3sp13SZC3SPR2F04SP1RFFFFS1P3END2B2FFS1R3NS15STKsi2sp2lo3SLO3LOSS2r13Hr1S1P3END2B2S1r2HrS1P3END2p13Hp12p'FS5PHIsi5CNTsi1P3END2p12Lw3SY24PHIx4HPXBFS5CNTsi1P3END3SZ1S2FB2F0S1R5STKsi2LF2sp2PP3SIG4DALG2bs2sj3LFB2FB3sp13SZCFS3BUF2bs3B47FS1i2HiFS1R2lo3LOSS1R5STKsi2sp2PP2lo4PPLO3SLO3sp13SP1S5PHIsi5CNTsi1P3END3SZ24PS00FFFS5FFRsi5CNTsi1P3END1d3SZ34FS004FRC03SZ4S1R3HIA1hS2p12p'2U4S1P3END2B2FS1r2Hr2r02KR1q1HS2FB2r03F641q1r1H2H02q02H43sp14SP1MFS2r13Hr11r2KT1q1HFFS2sp3sp1SS5CNTsi1P3END1XSSS2sp2lo3sp13SP1S1R5STKsi2sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFFFFFFFFFFFFFFFFFFS1R5STKsi2sp2lo3SLO3sp13SP1FFFS1R5STKsi2LF2sp2PP3SIG2lo2bs2sj3LFB4PPLO3SLO3sp13SP13SZC2HB5Ha_st5Hl_st4DALGS1R5STKsi2LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp15inext3sj'5nodes3SP13SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp3SIG2lo2bs2sj3LFB4SGLO3SLO3sp13SP13SZC2HB5Ha_st5Hl_st4DALGS1R5STKsi2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp15inext3sj'5nodes3SP13SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp3SIG2lo2bs2sj3LFB3SLO3LOS2FB3sp13SP13SZC3ALO2F12HB5Ha_st5Hl_st4DALGS1R5STKsi2LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13ALO5inext3sj'5nodes3SP13SZC2F12HB5Ha_st5Hl_stS1R5STKsi2LF2sp2PP2lo2bs2sj3LFB4PPLO3SLO3SZCS1R5STKsi2LF2sp3SIG4DALG2lo2bs2sj3LFB4DALO3SLO3sp13SP13SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp4DALG2lo2bs3LFB4DALO3SLO3sp15inext3sj'5nodes3SP13SZC2HB5Ha_st5Hl_stS1R3NS15STKsi2LF2sp2lo2bs2sj3LFB3SLO3LOS2FB3sp13SP13SZC3ALO2F1S1R5STKsi2LF2sp3SIG2lo2bs2sj3LFB3SLO3LOS2FB3sp13SP13SZC3ALO2F12HB5Ha_st5Hl_st4DALGS1R5STKsi2LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13ALO5inext3sj'5nodes3SP13SZC2F12HB5Ha_st5Hl_stS1R3NS15STKsi2LF2sp2lo2bs2sj3LFB3SLO3LOS2FB3SZC3ALO2F1S1R5STKsi2LF2sp3BUF3SIG2lo2bs2sj3LFB3SLO3LOS3sp13SP13SZC3ALO3BCE2HB5Ha_st5Hl_st4DALGS1R5STKsi2LF2sp3BUF2lo2bs3LFB3SLO3LOS3sp13ALO3BCE5inext3sj'5nodes3SP13SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp2lo2bs2sj3LFB3SLO3LOS2FB3sp13SP13SZC3ALO2F1S1R5STKsi2LF2sp2lo2bs2sj3LFB3SLO3LOS2FB3sp13SP13SZC3ALO2F1S1R5STKsi2LF2PP2lo2bs2sj3LFB4PPLO3sp13SZCS1R3NS15STKsi2LF2sp2PP2lo2bs2sj3LFB4PPLO3SLO3sp13SP13SZCS1R5STKsi2LF2sp3SIG2bs2sj3LFB3sp13SP13SZC2HB5Ha_st5Hl_st4DALGS1R5STKsi2LF2sp2bs3LFB3sp15inext3sj'5nodes3SP13SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp3SIG2lo2bs2sj3LFB4SGLO3SLO3sp13SP13SZCS1R5STKsi2LF2lo2bs2sj3LFB3LOS2FB3sp13SZC3ALO2F1S1R5STKsi2LF2sp4DALG2lo2bs2sj3LFB4DALO3SLO3sp13SP13SZCS1R5STKsi2LF2sp2bs2sj3LFB3sp13SP13SZCS1R5STKsi2LF2sp3BUF2lo2bs2sj3LFB3SLO3LOS3sp13SP13SZC3ALO3BCES1R5STKsi2LF2sp2PP2lo2bs2sj3LFB4PPLO3SLO3sp13SP13SZCS1R5STKsi2LF2bs2sj3LFB2FB3SZCS1R5STKsi2LF2bs2sj3LFB2FB3SZCS1R5STKsi2LF2bs2sj3LFB2FB3SZCS1R5STKsi2LF2PP2bs2sj3LFB3SZCS1R5STKsi2LF2PP2bs3LFB5inext3sj'5nodes3SZCS1R5STKsi2LF2PP2bs2sj3LFB3SZCS1R5STKsi2LF2PP2bs3LFB5inext3sj'5nodes3SZCS1R5STKsi2LF2PP2bs2sj3LFB3SZCS1R5STKsi2LF2bs2sj3LFB2FB3SZCFS1R5STKsi2LF2PP2bs3LFB5inext3sj'5nodes3SZCS1R5STKsi2LF2PP2bs2sj3LFB3SZCS1R5STKsi2LF2PP2bs2sj3LFB3SZCS1R5STKsi2LF2sp2PP2lo2bs2sj3LFB4PPLO3SLO3sp13SP13SZCS1R5STKsi2LF2PP2bs2sj3LFB3SZCS1R5STKsi2LF2PP2bs3LFB5inext3sj'5nodes3SZCS1R5STKsi2LF2sp2PP3SIG4DALG2bs2sj3LFB3PP03SG03DA02FB3sp13F643SZC3SPR2F04SP1RS1R5STKsi2LF2sp2lo2bs2sj3LFB3SLO3LOS3sp13SP13SZC3ALOFS1R5STKsi2LF2sp2lo2bs2sj3LFB3SLO3sp13SP13SZCS1R5STKsi2LF2bs2sj3LFB2FB3SZCS1R5STKsi2LF2sp3SIG2lo2bs2sj3LFB4SGLO3SLO3sp13SP13SZC2HB5Ha_st5Hl_st4DALGS1R5STKsi2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp15inext3sj'5nodes3SP13SZC2HB5Ha_st5Hl_stFS1R5STKsi2LF2sp2lo2bs2sj3LFB3SLO3sp13SP13SZCS1R5STKsi2LF2sp2lo2bs2sj3LFB3SLO3sp13SP13SZCS1R5STKsi2LF2sp2lo2bs3LFB3SLO3sp15inext3sj'5nodes3SP13SZCS1R5STKsi2LF2bs2sj3LFB3sp13SZCS1R5STKsi2LF2bs2sj3LFB3sp13SZC4SP1R2HBS1R5STKsi2LF2bs3LFB3sp14SP1R5inext3sj'5nodes3SZC2HBS1R5STKsi2LF2sp2bs2sj3LFB3sp13SP13SZCFFFS1R5STKsi2LF2sp2lo2bs2sj3LFB3sp13SP13SZCS1R5STKsi2LF2sp2lo2bs3LFB3SLO3sp15inext3sj'5nodes3SP13SZCS1R5STKsi2LF2sp3SIG2lo2bs2sj3LFB3sp13SP13SZC2HB5Ha_st5Hl_st4DALGS1R5STKsi2LF2sp2lo2bs3LFB3sp15inext3sj'5nodes3SP13SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp3SIG2lo2bs2sj3LFB3sp13SP13SZC2HB5Ha_st5Hl_st4DALGS1R5STKsi2LF2sp2lo2bs3LFB3sp15inext3sj'5nodes3SP13SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp2lo2bs3LFB3sp15inext3sj'5nodes3SP13SZCS1R5STKsi2LF2sp2lo2bs2sj3LFB3sp13SP13SZCS1R5STKsi2LF2sp2PP3SIG2lo2bs2sj3LFB4PPLO3SLO3sp13SP13SZC2HB5Ha_st5Hl_st4DALGS1R5STKsi2LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp15inext3sj'5nodes3SP13SZC2HB5Ha_st5Hl_stFFS1R5STKsi2LF2sp3SIG2lo2bs2sj3LFB3SLO3LOS3sp13SP13SZC3ALO2HB5Ha_st5Hl_st4DALGS1R5STKsi2LF2sp2lo2bs3LFB3SLO3LOS3sp13ALO5inext3sj'5nodes3SP13SZC2HB5Ha_st5Hl_stFS1R5STKsi2LF2bs2sj3LFB2FB3SZCS1R5STKsi2LF3slo2bs2sj3LFB4SLOS3SZCS1R5STKsi2LF3SIG3slo2bs2sj3LFB4SLOS3sp13SZC2HB5Ha_st5Hl_st4DALGS1R5STKsi2LF3slo2bs3LFB4SLOS3sp15inext3sj'5nodes3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2PP2bs2sj3LFB3SZCS1R5STKsi2LF2PP2bs3LFB5inext3sj'5nodes3SZCS1R5STKsi2LF2PP2bs2sj3LFB3SZCS1R5STKsi2LF2sp2lo2bs2sj3LFB3SLO3LOS3SZC3ALOS1R5STKsi2LF2bs2sj3LFB2FB3SZCS1R5STKsi2LF2bs2sj3LFB3sp13SZC2HB5Ha_stS1R5STKsi2LF2bs3LFB3sp15inext3sj'5nodes3SZC2HB5Ha_stFFS1R5STKsi2LF2sp3SIG2bs2sj3LFB3sp13SP13SZC2HB5Ha_st5Hl_st4DALGS1R5STKsi2LF2sp2bs3LFB3sp15inext3sj'5nodes3SP13SZC2HB5Ha_st5Hl_stFFFS1R5STKsi2LF2sp3SIG2lo2bs2sj3LFB3SLO3sp13SP13SZC2HB5Ha_st5Hl_st4DALGS1R5STKsi2LF2sp2lo2bs3LFB3SLO3sp15inext3sj'5nodes3SP13SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp3SIG2lo2bs2sj3LFB3SLO3sp13SP13SZC2HB5Ha_st5Hl_st4DALGS1R5STKsi2LF2sp2lo2bs3LFB3SLO3sp15inext3sj'5nodes3SP13SZC2HB5Ha_st5Hl_stFFFFFFS1R5STKsi2LF2sp2PP3SIG4DALG2bs2sj3LFB3ALP3PP02FB3sp13SZC3SPR2F04SP1RS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB3ALP3PP02FB3sp13SPR4SP1R5inext3sj'5nodes3SZC2F0S1R5STKsi2LF2sp3SIG2lo2bs2sj3LFB4SGLO3SLO3sp13SP13SZCS1R5STKsi2LF2sp2lo2bs3LFB3sp15inext3sj'5nodes3SP13SZCS1R3HIA5STKsi1h2LF2sp3SIG3slo2bs2sj3LFB3TOP3sp13SZC2HT2HB5Ha_st5Hl_st4DALGS1R3HIA5STKsi1h2LF2sp3slo2bs3LFB3TOP3sp15inext3sj'5nodes3SZC2HT2HB5Ha_st5Hl_stS1R3HIA5STKsi1h2LF2sp3slo2bs2sj3LFB3TOP3SZC2HTFS1R5STKsi2LF2sp2lo2bs2sj3LFB3sp13SP13SZCS1R5STKsi2LF2bs2sj3LFB3sp13SZC4SP1RS1R5STKsi2LF2bs2sj3LFB2FB3SZC2F0S1R5STKsi2LF2bs2sj3LFB2FB3SZC2F0". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND CALLOC FREE GETTAG STKsi SIGNER PHIsi_mono FFRsi_mono CNTsi_mono PHIsi_sadd FFRsi_sadd CNTsi_sadd LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALS SG0 CWS SGLO DSB ALD DA0 CRDA DALO Q1 Q2 Q3 D1 D2 D3 SLOS SLOL SLO TOP SPA SPH TPV LOS"] Lemma from_S1P :
    havol asegs R HIA h + PHIs PHIsi CNTsi NB <= AVOL_MAX -> hfr asegs R HIA h + FFRs FFRsi CNTsi NB d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    forall ms, S1P ms -> aevtA asegs (KF asegs R HIA h mo0) POST ms.
  Proof.
    intros BUD BUDF UW ms HS1.
    ddestruct HS1 as (FB & sp1 & h1 & m1 & x1 & t0 & t1 & t2 & a0 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & w0 & w1 & w2 & k0 & k8 & k16 & j32
                    & Ems & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & G4 & FSH & SAVE & RSL & SThi & STlo & MI1
                    & PPc & CSG & DAc & BYc & OPP & OSG & ODA & OBUF & APP0 & APS0 & APD0 & APB0 & PRES0 & SS1).
    subst ms. intros moc [HK0c MF0c].
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as Dnn.
    pose proof (CNTsi_mono 0 NB ltac:(clear - B1 B2; lia)) as CS0'. pose proof (PHIsi_mono 0 NB ltac:(clear - B1 B2; lia)) as PS0. pose proof (FFRsi_mono 0 NB (d + 1) ltac:(clear - B1 B2; lia)) as FS0.
    assert (NB0 : 0 <= NB) by (clear - B2; lia).
    (* [comment removed for export] *)
    pose proof (A_pkcs7_signers_C.sinv_bounds PHIsi FFRsi CNTsi PHIsi_mono FFRsi_mono CNTsi_mono PHIsi_sadd FFRsi_sadd d 0 0 0 0 0 NB Dnn
                  (A_pkcs7_signers_C.sinv_zero PHIsi FFRsi CNTsi PHIsi_mono FFRsi_mono CNTsi_mono d Dnn) NB0) as (SZ1 & SZU).
    destruct (SZU 0 ltac:(clear; lia) NB0) as (SZ2 & SZ3).
    pose proof (PHIsi_mono 0 0 ltac:(clear; lia)) as PS00. pose proof (FFRsi_mono 0 0 (d + 1) ltac:(clear; lia)) as FS00.
    assert (FRC0 : 0 <= fr_charge (d + 1)) by (unfold fr_charge; clear - Dnn; lia).
    assert (SZ4 : 0 <= (A_pkcs7_signers_C.CNTs CNTsi NB + 1) * fr_charge (d + 1)) by (apply Z.mul_nonneg_nonneg; [clear - SZ1; lia| exact FRC0]).
    assert (SZ5 : CNTsi NB <= A_pkcs7_signers_C.CNTs CNTsi NB) by (unfold A_pkcs7_signers_C.CNTs; pose proof (Z.div_pos NB 2 NB0 ltac:(clear; lia)) as X; clear - X; lia).
    (* [comment removed for export] *)
    assert (G1 : gvA FB sp1 X0 0 0 w0 w1 w2 (Z_to_bv 64 0) (Z_to_bv 8 0) k0 k8 k16 (Z_to_bv 64 DALG) j32 P (signer_cells 0 0 sj) [] m1 moc h1).
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
      split; [exact PPc|]. split; [clear - B2; lia|]. split; [exact CSG|]. split; [reflexivity|]. split; [exact DAc|]. split; [exact BYc|].
      split; [exact OPP|]. split; [exact OSG|]. split; [exact ODA|]. split; [exact OBUF|]. split; [exact MI1| exact SS1]. }
    clear HH1 HKI FHD G4 FSH SAVE RSL SThi STlo MI1 PPc CSG DAc BYc OPP OSG ODA OBUF PRES0 SS1 SP1 SP1M F64 FRSH Ehtop Estk Eflag Evol Efr.
    pose proof G1 as D. gvA_open D. rt_facts. walk_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 STKsi0 NRT; lia).
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
      (eapply GT' with (CS := hcs asegs R HIA h1) (PP := PP) (LENP := FB + 32) (P := P) (END := END) (BUF := BUF) (bs := bs) (tag := 49) (lo := lo) (lenv := Z_to_bv 64 0);
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
                 | |- lo <= sp1 - 16 => clear - SLO SP1 NS1 STKsi0 NRT; lia
                 | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                 | |- crange _ lo _ => eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]
                 | |- PP + 8 <= sp1 - 16 \/ _ => left; clear - PPLO SLO SP1 NS1 STKsi0 NRT; lia
                 | |- FB + 32 + 8 <= sp1 - 16 \/ _ => left; clear - F1 ALO LOS SLO SP1 NS1 STKsi0 NRT; lia
                 | |- n = 0 \/ BUF + n <= sp1 - 16 \/ _ => right; left; clear - BCE ALO LOS SLO SP1 NS1 STKsi0 NRT; lia
                 end
               | match goal with |- ?g => idtac "GT-PRE-LEFT:" g end ]).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "GT-LEFT:" g end.
    clear GT' ABc OL.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r1 end.
    match goal with H : _ < r1 <= 0 |- _ => rename H into Hr1 end.
    match goal with H : r1 = 0 -> _ |- _ => rename H into HOK1 end.
    match goal with H : P <= ?pp <= END |- _ => rename H into Hp1; rename pp into p1 end.
    lazymatch goal with H : rw_cells _ ?mx (FB + 32) [C8 ?lw] |- _ => rename lw into Lw; rename H into G4'; rename mx into m2 end.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    (* [comment removed for export] *)
    zstep. if_cases KT; zify_cond KT.
    2:{ (* [comment removed for export] *)
        zstep. zstep. zstep.
        first [ rewrite (swrap32_land_errsum r1 18446744073709529472) by (clear - Hr1; lia)
              | match goal with |- ?g => idtac "ADDW-FORM:" g end ].
        zpre.
        intros moq [HKq MFq].
        eapply (ret_walk R HIA) with (STKsi := STKsi) (names0 := []) (sg := []) (inext := 0) (snext := 0) (sj' := sj)
                                     (PHIa := 0) (FFRa := 0) (slo := slo) (d := d) (lo := lo) (hc := h1) (mc := m2) (moc := moq) (Lc := []) (W := X0) (r := r1 + (18446744073709529472 - 2 ^ 64));
          first [ sec_hyps
                | lazymatch goal with
                  | |- name_chain _ _ _ _ _ _ => cbn; reflexivity
                  | |- signer_chain _ _ _ _ _ => reflexivity
                  | |- Permutation _ _ => apply Permutation_refl
                  | |- Z.of_nat (length []) <= _ => cbn [length Z.of_nat]; clear - SZ1; lia
                  | |- 0 <= A_pkcs7_signers_C.PHIs _ _ _ => unfold AVOL_CALL in *; clear - SZ2 PS00; lia
                  | |- 0 <= A_pkcs7_signers_C.FFRs _ _ _ _ => clear - SZ3 SZ4 FS00 FRC0; lia
                  | |- forall x, outside _ x -> outside _ x => intros xq Hxq; exact Hxq
                  | |- _ < _ < _ => clear - Hr1; lia
                  end
                | (lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signers_C.gvA] => idtac end end;
                   eapply gvA_mo; [| exact HKq| exact MFq]; gvA_fin HKc MFc (mo_frame_refl moc))
                | match goal with |- ?g => idtac "HEAD-RET1-LEFT:" g end ]. }
    assert (R10 : r1 = 0).
    { change 18446744073709551615 with (Z.ones 64) in KT. rewrite ?Z.land_ones in KT by (clear; lia). clear - KT Hr1. Z.div_mod_to_equations. lia. }
    subst r1. destruct (HOK1 eq_refl) as [Hp1a HLw]. clear HOK1 KT Hr1.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases KL; zify_cond KL.
    { (* [comment removed for export] *)
      zstep. zstep.
      intros moq [HKq MFq].
      eapply (ret_walk R HIA) with (STKsi := STKsi) (names0 := []) (sg := []) (inext := 0) (snext := 0) (sj' := sj)
                                   (PHIa := 0) (FFRa := 0) (slo := slo) (d := d) (lo := lo) (hc := h1) (mc := m2) (moc := moq) (Lc := []) (W := X0) (r := 0);
        first [ sec_hyps
              | lazymatch goal with
                | |- name_chain _ _ _ _ _ _ => cbn; reflexivity
                | |- signer_chain _ _ _ _ _ => reflexivity
                | |- Permutation _ _ => apply Permutation_refl
                | |- Z.of_nat (length []) <= _ => cbn [length Z.of_nat]; clear - SZ1; lia
                | |- 0 <= A_pkcs7_signers_C.PHIs _ _ _ => unfold AVOL_CALL in *; clear - SZ2 PS00; lia
                | |- 0 <= A_pkcs7_signers_C.FFRs _ _ _ _ => clear - SZ3 SZ4 FS00 FRC0; lia
                | |- forall x, outside _ x -> outside _ x => intros xq Hxq; exact Hxq
                | |- _ < 0 < _ => clear; lia
                end
              | (lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signers_C.gvA] => idtac end end;
                 eapply gvA_mo; [| exact HKq| exact MFq]; gvA_fin HKc MFc (mo_frame_refl moc))
              | match goal with |- ?g => idtac "HEAD-RET0-LEFT:" g end ]. }
    assert (LNZ : bv_unsigned Lw <> 0) by (intros E; rewrite E in KL; cbv in KL; first [exact (KL eq_refl) | congruence | lia]).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    match goal with |- context [Z_to_bv 64 (p1 + bv_unsigned Lw)] => idtac | |- ?g => idtac "ENDSET-FORM:" g end.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      assert (G2 : gvA FB sp1 X0 0 0 w0 w1 w2 Lw (Z_to_bv 8 0) k0 (Z_to_bv 64 SIG) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 DALG) j32 p1 (signer_cells 0 0 sj) [] mx moc h1)
        by (gvA_fin HKc MFc (mo_frame_refl moc));
      rename mx into m2'
    end.
    try clear HHc. try clear HKc. try clear MFc. try clear HTc. try clear HSc. try clear HFc. try clear HCSc. try clear HVc. try clear HFRc. try clear PRES. try clear SP1. try clear SP1M. try clear F64. try clear FRSH. try clear CFB. try clear FHD. try clear G4. try clear G4'. try clear FSH. try clear SAVE. try clear RSL. try clear STb. try clear STlo. try clear PPc. try clear Hpc. try clear CSG. try clear SZC. try clear DAc. try clear BYc. try clear OPP. try clear OSG. try clear ODA. try clear OBUF. try clear MIc. try clear SSc. try clear OPPc. try clear OSGc. try clear ODAc. try clear OBUFc. try clear D. try clear G1. try clear CSOKc. try clear HT. try clear CFBc. try clear SCS03c. try clear SCS. try clear SCSc. try clear CRP. try clear CRS. try clear CRDg. try clear APP. try clear APSG. try clear F0. try clear F1. try clear F2. try clear F3. try clear STKH. try clear WL. try clear WCS. try clear WCP. try clear CWSc. try clear CWPc. try clear ABc.
    destruct (SZU (p1 + bv_unsigned Lw - p1) ltac:(clear - LR; lia) ltac:(clear - HLw Hp1 LR; lia)) as (SY2 & SY3).
    eapply (signer_step_head R HIA) with (STKsi := STKsi) (hc := h1) (moc := moc) (mc := m2') (Lc := []) (sjs := sj) (ENDx := p1 + bv_unsigned Lw)
                                          (PHIa := 0) (FFRa := 0) (slo := slo) (d := d) (lo := lo) (p := p1)
                                          (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0)
                                          (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
      first [ exact G2 | exact UW | sec_hyps
            | lazymatch goal with
              | |- p1 <= p1 + _ => clear - LR; lia
              | |- p1 + _ <= END => clear - HLw Hp1; lia
              | |- havol _ _ _ _ + _ + _ <= _ => unfold AVOL_CALL in *; clear - BUD SY2; lia
              | |- hfr _ _ _ _ + _ + _ <= _ => clear - BUDF SY3 SZ4 FRC0; lia
              | |- 0 <= _ < 2 ^ 64 => clear; lia
              | |- _ mod 2 = 0 => reflexivity
              | |- forall m3 mo3 h3, _ => idtac
              end
            | match goal with |- ?g => idtac "HEAD-SIGNER-LEFT:" g end ].
    cbv beta. intros m3 mo3 h3 r p' inext sj' nodes PHIx FFRx z0 z1 z2 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 G3 Hr Hp' Hprog Hnodes HNC3 HND3 HAP3 HCNT3 HPXB HFXB HSUC HPX3.
    rewrite app_nil_r in G3.
    assert (HNC3' : name_chain asegs (fun _ => True) m3 (SNAME (rev nodes) ++ LB) inext nodes).
    { eapply chain_mem; [exact HNC3| intros xq Hxq; apply in_or_app; left; apply SNAME_in; exact Hxq| intros xq cs _ HR _; exact HR]. }
    clear HNC3. rename HNC3' into HNC3.
    pose proof G3 as D. gvA_open D. walk_prep.
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h3) as LAWS. pose proof (KF_kinv asegs R HIA h3 mo3) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KR; zify_cond KR.
    { (* [comment removed for export] *)
      assert (RNZ : r <> 0) by (intros E; rewrite E in KR; cbv in KR; first [exact (KR eq_refl) | congruence | lia]).
      specialize (Hnodes RNZ). subst nodes. cbn [rev SNAME map app] in G3, HNC3.
      intros moq [HKq MFq].
      eapply (ret_walk R HIA) with (STKsi := STKsi) (names0 := []) (sg := []) (inext := inext) (snext := 0) (sj' := sj')
                                   (PHIa := 0 + PHIx) (FFRa := 0 + FFRx) (slo := slo) (d := d) (lo := lo) (hc := h3) (mc := m3) (moc := moq) (Lc := []) (W := X0) (r := r);
        first [ sec_hyps
              | lazymatch goal with
                | |- name_chain _ _ _ _ _ _ => exact HNC3
                | |- signer_chain _ _ _ _ _ => reflexivity
                | |- Permutation _ _ => apply Permutation_refl
                | |- Z.of_nat (length []) <= _ => cbn [length Z.of_nat]; clear - SZ1; lia
                | |- 0 + _ <= A_pkcs7_signers_C.PHIs _ _ _ => unfold AVOL_CALL in *; clear - SY2 HPXB; lia
                | |- 0 + _ <= A_pkcs7_signers_C.FFRs _ _ _ _ => clear - SY3 SZ4 HFXB FRC0; lia
                | |- forall x, outside _ x -> outside _ x => intros xq Hxq; exact Hxq
                | |- _ < r < _ => clear - Hr; lia
                end
              | eapply gvA_mo; [exact G3| exact HKq| exact MFq]
              | match goal with |- ?g => idtac "HEAD-RETR-LEFT:" g end ]. }
    assert (R0 : r = 0).
    { first [change 18446744073709551615 with (Z.ones 64) in KR; rewrite ?Z.land_ones in KR by (clear; lia) | idtac]. clear - KR Hr. Z.div_mod_to_equations. lia. }
    subst r. specialize (Hprog eq_refl). clear KR Hnodes.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    zstep. if_cases KE; zify_cond KE;
      first [change 18446744073709551615 with (Z.ones 64) in KE; rewrite !Z.land_ones in KE by (clear - Hp' Hp1 HLw B1 B2 B3 B47 B5 LR; lia) | idtac];
      rewrite ?Z.mod_small in KE by (clear - Hp' Hp1 HLw B1 B2 B3 B47 B5 LR; lia).
    { (* [comment removed for export] *)
      zstep.
      intros moq [HKq MFq].
      eapply (ret_walk R HIA) with (STKsi := STKsi) (names0 := nodes) (sg := []) (inext := inext) (snext := 0) (sj' := sj')
                                   (PHIa := 0 + PHIx) (FFRa := 0 + FFRx) (slo := slo) (d := d) (lo := lo) (hc := h3) (mc := m3) (moc := moq) (Lc := SNAME (rev nodes)) (W := X0) (r := 1);
        first [ sec_hyps
              | lazymatch goal with
                | |- name_chain _ _ _ _ _ _ => exact HNC3
                | |- signer_chain _ _ _ _ _ => reflexivity
                | |- Permutation _ _ => cbn [signer_blocks]; rewrite app_nil_r; apply perm_SNAME_rev
                | |- Z.of_nat (length _) <= _ => unfold SNAME; rewrite length_map, length_rev; clear - SZ5 HCNT3; lia
                | |- 0 + _ <= A_pkcs7_signers_C.PHIs _ _ _ => unfold AVOL_CALL in *; clear - SY2 HPXB; lia
                | |- 0 + _ <= A_pkcs7_signers_C.FFRs _ _ _ _ => clear - SY3 SZ4 HFXB FRC0; lia
                | |- forall x, outside _ x -> outside _ x => intros xq Hxq; exact Hxq
                | |- _ < 1 < _ => clear; lia
                end
              | eapply gvA_mo; [exact G3| exact HKq| exact MFq]
              | match goal with |- ?g => idtac "HEAD-RETONE-LEFT:" g end ]. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      pose proof (presW_init_at R HIA h3 _ _ (SNAME (rev nodes) ++ LB) LF mx (bv_unsigned sp) (bv_unsigned sp) [] h HHc
                    ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSc HSc ltac:(clear - LOS SLO NS1 STKsi0 NRT; lia)) as PRESq;
      rename mx into m4
    end.
    zstep. zstep. zstep. zstep.
    lazymatch goal with H : rw_cells _ _ sp1 [C8 ?va0; _; _; _; _; _] |- _ =>
      first [ replace va0 with (Z_to_bv 64 (-22400) : word) in H by (apply bv_eq; vm_compute; reflexivity)
            | idtac "SPILL-FORM:" va0 ] end.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m5 end.
    assert (HNC5 : name_chain asegs (fun _ => True) m5 (SNAME (rev nodes) ++ LB) inext nodes).
    { lazymatch goal with PQ : presW _ _ _ h3 (SNAME (rev nodes) ++ LB) LF _ _ [] m4 m5 |- _ =>
        eapply (chain_presx asegs L _ _ _ m4 m5 _ _ (bv_unsigned sp) []);
          [ exact HNC3 | intros xq Hxq; eapply (chain_nodes_in asegs); [exact HNC3| exact Hxq]
          | eapply heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA _ _ _ _ _ _ _ _ PQ))| intros b Hb; apply in_or_app; left; exact Hb| apply Z.le_refl| intros xq Hxq; exact Hxq]
          | unfold NAME_SIZE; clear; lia | intros; exact I ]
      | |- _ => fail "from_S1P: the h3-anchored bundle was dropped by the spill" end. }
    intros moq [HKq MFq].
    eapply (LOOP0 R HIA) with (STKsi := STKsi) (ES := p1 + bv_unsigned Lw) (p := p') (PHIa := 0 + PHIx) (FFRa := 0 + FFRx) (names0 := nodes) (inext0 := inext) (sjh := sj')
                               (slo := slo) (d := d) (lo := lo) (hc := h3) (moc := moq)
                               (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
      first [ exact UW | exact BUD | exact BUDF | exact HNC5 | sec_hyps
            | lazymatch goal with
              | |- A_pkcs7_signers_C.SINV _ _ _ _ _ _ _ _ _ =>
                  ddestruct (HSUC ltac:(assumption || reflexivity)) as (U1 & U2 & U3 & U4);
                  eapply (A_pkcs7_signers_C.sinv_head PHIsi FFRsi CNTsi PHIsi_mono FFRsi_mono CNTsi_mono d (p' - P) (p' - p1)); [exact Dnn| clear - U4; lia| clear - Hp1; lia| exact U1| exact U2| exact U3]
              | |- P < p' => clear - Hprog Hp1; lia
              | |- p' < p1 + _ => clear - KE Hp'; lia
              | |- p1 + _ <= END => clear - HLw Hp1; lia
              end
            | (lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signers_C.gvA] => idtac end end;
               eapply gvA_mo; [| exact HKq| exact MFq]; gvA_fin HKc MFc (mo_frame_refl mo3))
            | match goal with |- ?g => idtac "HEAD-LOOP0-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG UARG SM0 NS1 DIMG HMND CALLOC FREE GETTAG SIGNER PHIsi_mono FFRsi_mono CNTsi_mono PHIsi_sadd FFRsi_sadd CNTsi_sadd"] Theorem A_pkcs7_getsigners_spec :
    pkcs7_getsigners_stmtA asegs R HIA (PHIs PHIsi CNTsi) (FFRs FFRsi CNTsi) (CNTs CNTsi) STKs A_PKCS7_GETSIGNERS.
  Proof.
    intros h LB LF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo PP P END BUF SIG DALG lo slo d bs dtg dpad dlen dq sj.
    intros HH HK0 LFB HPP ALP PP0 OPP CWP PPLO HBY BIN B1 B2 B3 B47 B5 B30 DPB HSG ALS SG0 OSG CWS SGLO DSB HDA ALD DA0 ODA CRDA DALO Q1 Q2 Q3 D1 D2 D3
           ST SS SLOS SLOL SLO TOP SPA SPH MI TPV NDL BUD UW BUDF -> -> -> ->.
    pose proof (hm_aobj_block asegs R HIA h _ _ m BUF (Z.of_nat (length bs)) HH BIN) as OBUF.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ _ (conj HK0 (mo_frame_refl mo))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo).
    { eapply (pro_walk R HIA) with (STKsi := STKsi) (lo := lo) (slo := slo) (bs := bs) (P := P) (END := END) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq) (sj := sj);
        first [ exact HH | exact HPP | exact HBY | exact HSG | exact HDA | exact CWP | exact CWS | exact CRDA | exact ST | exact SS | exact OPP | exact OSG | exact ODA | exact OBUF | exact SLO
              | eassumption | match goal with |- ?g => idtac "PW-LEFT:" g end ]. }
    intros ms1 HS1.
    eapply from_S1P with (bs := bs);
      first [ exact HPP | exact HBY | exact HSG | exact HDA | exact CWP | exact CWS | exact CRDA | exact SLO | exact BUD | exact UW | exact BUDF | exact HS1 | exact ST | exact SS
            | eassumption | match goal with |- ?g => idtac "FS-LEFT:" g end ].
  Qed.
End Walk.
