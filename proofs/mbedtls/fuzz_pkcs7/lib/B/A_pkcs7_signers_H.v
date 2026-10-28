(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_pkcs7_signers.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag
     A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt A_pkcs7_signers_A A_pkcs7_signers_B A_pkcs7_signers_C A_pkcs7_signers_D A_pkcs7_signers_E A_pkcs7_signers_F A_pkcs7_signers_G.
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
  Hypothesis STKsi0 : 0 <= STKsi.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55853786883.20000003S1R". (* [comment removed for export] *)
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
          | exact PHIsi_mono | exact FFRsi_mono | exact CNTsi_mono | exact STKsi0
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L29367582956.10300000OS2LF2sp2PP3SIG4DALG2bs3LFB2ns1r". (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00_0@D12949562016.219D25662884252.219D60109196847.219K12838370724.219K28788825731.219K44164039966.219K49341710523.219K49936266399.219L12850865746.2  L1685717371.0   L2036051503.2   L27111942217.1  L28776318325.2  L32280122272.2  L35666023782.12 L38308634325.0  L39332637397.0  L40228640085.0  L42927756920.1  L44168742175.3  L49326776262.2  L49493397620.5  L49936279650.2  L60098763854.6  P2042605906.219 P32294539623.219Q12949562016.219Q12951513248.218Q21157640433.217Q21925682067.215Q23258654747.219Q25660900252.218Q25662884252.219Q27942899219.215Q28337929679.216Q35288190350.215Q42219631003.216Q42439443119.219Q47457724444.215Q4821847645.215 Q4825674107.216 Q59196635902.215Q59865321072.219Q64683667846.219Q66337817851.216Q67183863355.216Q7522361358.215 00001402803C04=05706106i07c07d07e07f07j07k07l08H08I08J08K08P08Q08R08\08]08g09h0;10;c0<U0=A0>60>70>i0?[0@P0A30A`0CH0DC0Df0EI0El0FO0FP0GV0GW0HA0HnS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13snx3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13snx3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3LOS2FB3sp13snx3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF3SIG2bs3LFB2FB3snx3sjh3SZC4APSG2HB5Ha_st5Hl_stS1R5STKsi2LF3SIG2bs3LFB2FB3snx3sjh3SZC4APSG2HB5Ha_st5Hl_stS1R5STKsi2LF3BUF3SIG2bs3LFB3DSB3snx3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2PP3SIG2bs3LFB2D13snx3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF3SIG4DALG2bs3LFB2D33snx3sjh3SZC2HB5Ha_st5Hl_stFSFS2PPFFS1R3HIA5STKsi1h2sp2lo3TOP2HTSSSS3SIGFFS1P3END2B2FS1R2lo3LOSS1R5STKsi2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3snx3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13snx3sjh3SP13SZC2HB5Ha_st5Hl_stS1R5STKsi2LF3SIG2bs3LFB3snx3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF3SIG2bs3LFB3snx3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF3SIG2bs3LFB3snx3sjh3SZC2HB5Ha_stS1R3NS15STKsi2LF2sp2lo2bs3LFB3SLO3sp13snx3sjh3SP13SZCFS1R5STKsi2LF3SIG2bs3LFB3snx3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF3SIG2bs3LFB3snx3sjh3SZC2HB5Ha_st5Hl_stS1R3NS15STKsi2LF2sp2lo2bs3LFB3SLO3sp13snx3sjh3SP13SZCS1R5STKsi2LF3SIG2bs3LFB3snx3sjh3SZCS1R5STKsi2LF2sp2lo2bs3LFB3sp13snx3sjh3SP13SZCS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03ALS3SG03DA03SLO3LOS2FB3sp13snx3sjh3SP14SP1M3SZC3ALO3ACV3SPR2F0S1R5STKsi2LF3SIG3slo2bs3LFB4SLOS3snx3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF3SIG2bs3LFB3snx3sjh3SZCS1R5STKsi2LF3SIG2bs3LFB3snx3sjh3SZCS1R5STKsi2LF3SIG2bs3LFB3snx3sjh3SZCS1R5STKsi2LF3SIG2bs3LFB3snx3sjh3SZCFS1R3HIA5STKsi1h2LF2sp3SIG3slo2bs3LFB3TOP3snx3sjh3SZC2HT2HB5Ha_st5Hl_stFS1R5STKsi2LF3SIG2bs3LFB3SG03snx3sjh3SZC2HBS1R5STKsi2LF2sp2lo2bs3LFB3sp13snx3sjh3SP13SZC". (* [comment removed for export] *)
  #[using="IMG NS1 STKsi CNTsi_mono LFB PP0 CWP PPLO B2 DPB ALS SG0 CWS SGLO DSB DA0 CRDA DALO D1 D2 D3 SLOS SLOL SLO TOP SPH LOS"] Lemma CL_END : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 : word) (j32 : list byte)
      (p snx : Z) (sjh : signer_junk) mc moc hc (r : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s7v s8v s11v : word),
    gvA FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 k0 k8 (Z_to_bv 64 (Z.shiftr (SIG + 192) 3 + al_sb AL)) (Z_to_bv 64 (SIG + 192)) j32 p (signer_cells 0 snx sjh) [] mc moc hc ->
    PHIa <= PHIs PHIsi CNTsi NB -> FFRa <= FFRs FFRsi CNTsi NB d -> -2^31 < r < 2^31 ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 FB) (Z_to_bv 64 r) s7v s5v s6v (Z_to_bv 64 (al_sb AL)) s8v (Z_to_bv 64 FB)
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) s11v t3 t4 t5 t6)
                 F (Z_to_bv 64 0x98e0c) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s11v. intros D PHI FFR Hr. pose proof D as D0. gvA_open D. rt_facts. walk_prep.
    unfold signer_cells in CSG. cbn [sj0 sj_merged sj1 sj2] in CSG.
    pose proof (CNTsi_mono 0 NB ltac:(clear - B1 B2; lia)) as CS0'.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    intros mo9 [HK9 MF9].
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) =>
    eapply (ret_walk R HIA) with (STKsi := STKsi) (hc := hc) (Lc := @nil blk) (names0 := @nil Z) (sg := @nil (Z * list Z)) (inext := 0) (snext := 0) (sj' := sjh)
                              (PHIa := PHIa) (FFRa := FFRa) (W := X0) (p := p) (slo := slo) (d := d) (lo := lo);
      first [ exact PHI | exact FFR | exact Hr | sec_hyps
            | lazymatch goal with
              | |- name_chain _ _ _ _ 0 [] => apply chain_nil
              | |- signer_chain _ _ _ 0 [] => reflexivity
              | |- Permutation [] _ => apply Permutation_refl
              | |- Z.of_nat (length []) <= _ => cbn [length]; change (Z.of_nat 0) with 0; unfold A_pkcs7_signers_C.CNTs; clear - CS0' B1 B2; nia
              | |- forall x, outside X0 x -> outside X0 x => intros x Hx; exact Hx
              end
            | gvA_fin HK9 MFc MF9
            | eassumption
            | match goal with |- ?g => idtac "CLEND-LEFT:" g end ]
    end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0?L19980016842.7 L22706555394.8 L23615739305.3 L26892418956.1 L29655710244.6 L31786234442.25L33562756752.7 L49799904432.3 L56658999053.1 L58790154276.10L62018535662.1 L62037211595.13L6203936179.1  L66151427842.16L696052593.2   L7371043258.8  L8387365206.3  L8464131484.15 L9356559676.17 L9838743115.2  00000H00d00n01201D02G02`02l03003O03R04;04@04c04k05H05T06706b06lS1R3HIA1h2sp3TOP3sp13SP1S1x1k3wlo3whi4HWlo4HWhi1q2HqS1R3HIA2hcS2spS1x1k3wlo3whi4HWhiS1R3HIA5STKsi1h2sp2lo3SLO3LOS3sp11x1k3wlo3whi3SP14HWhi3ALO3XCE1a2HaS1R3HIA1h4PHIa2hc3HVc3BUDS2sp3sp13SP1S2spS1R5STKsi3NRT2sp2lo3SLO3sp13SP1S1RS1R3NS15STKsi2sp2lo3slo4SLOS4SLOL3SLO3SPRS3sp1S2sp2r03SPA1q1r1H2H02q02H43sp14SP1MS2sp3SPRS1R3HIA1h1d4FFRa2hc4HFRc4BUDFS1x3wlo4HWloS1R5STKsi2sp2lo3SLO3LOS3sp13SP13ALOS1R5STKsi2sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS3sp14SP1R". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG STKsi NRT CWP PPLO BIN CWS SGLO CRDA DALO SLOS SLOL SLO TOP SPA TPV LOS"] Lemma free_stepA_st : forall (FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p : Z) (sgc : list cell) (Lc : list blk) mc moc hc (x k wlo whi : Z) (ms : mem) (RET : Z) (Q : config -> Prop)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
    gvA FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc mc moc hc ->
    In (x, k) Lc -> List.NoDup (map fst (Lc ++ LB)) ->
    munch [(wlo, whi)] mc ms -> wmono asegs mc ms -> x <= wlo -> whi <= x + k ->
    HM asegs R HIA hc (Lc ++ LB) ((FB, 64) :: LF) ms -> mem_inv asegs ms -> stk asegs ms lo sp1 ->
    havol asegs R HIA h + PHIa + AVOL_CALL <= AVOL_MAX -> hfr asegs R HIA h + FFRa + fr_charge (d + 1) <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    (forall a, bv_unsigned sp <= a < hstkhi asegs R HIA h -> outside W a) ->
    0 <= RET < 2^64 -> RET mod 2 = 0 ->
    (forall m1 mo1 h1 (y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
        gvA FB sp1 W (PHIa + AVOL_CALL) (FFRa + fr_charge (d + 1)) w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc (lb_remove x Lc) m1 mo1 h1 ->
        presA asegs R (lb_remove x (Lc ++ LB)) ((FB, 64) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m1 ->
        aevtA asegs (KF asegs R HIA h1 mo1) Q
          (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 sp1) gp tp y0 y1 y2 sp (Z_to_bv 64 sp1) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                   s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v y3 y4 y5 y6)
              F (Z_to_bv 64 RET) fc None m1 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc moc) Q
      (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
          F (Z_to_bv 64 (arl_free R)) fc None ms (seg_rom asegs)).
  Proof.
    intros until s11v. intros D HIN ND MU WM HWlo HWhi HHs MIs STs BUD BUDF UW WST RETR RETE K. pose proof D as D0. gvA_open D. rt_facts.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT. rewrite HTc, HSc in HT.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 STKsi0 NRT; lia).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0'.
    pose proof (blocks_below_hm R HIA hc _ _ mc _ HHc ltac:(intros b Hb; exact Hb)) as BBc.
    destruct (BBc (x, k) ltac:(apply in_or_app; left; exact HIN)) as [_ XCE]. cbn [fst snd] in XCE.
    assert (UW1 : uwc asegs ms (arl_stklo R) (hstkhi asegs R HIA hc) (bv_unsigned sp) sp1 (d + 1)).
    { rewrite HSc.
      assert (UWa : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
      { eapply (uwc_presA R); [exact (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES)| exact UW| clear; lia| exact WST| clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO SPR NS1 STKsi0 NRT; lia]. }
      pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_munch asegs [(wlo, whi)] mc ms);
        [ eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UWa| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0']
        | exact MU | clear - SP1R; lia | apply hstkhi_le64; clear - LOS SLO SPR NS1 STKsi0 NRT; lia
        | intros a Ha; cbn [outside]; split; [clear - Ha HWhi XCE ALO LOS SLO SP1 NS1 STKsi0 NRT; lia| exact I] ]. }
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_free asegs R HIA) with (h := hc) (LB := Lc ++ LB) (LF := (FB, 64) :: LF) (A := x) (n := k) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HHs | exact HK1 | exact LOS | exact TPV | exact UW1 | reflexivity
              | lazymatch goal with
                | |- In (x, k) (Lc ++ LB) => apply in_or_app; left; exact HIN
                | |- stk _ _ lo _ => exact STs
                | |- mem_inv _ _ => exact MIs
                | |- lo <= sp1 - arl_need_free R => clear - SLO SP1 NS1 STKsi0 NRT; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD HVc; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDF HFRc; lia
                end
              | match goal with |- ?g => idtac "FREEST-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms2 mo2x dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2' & mo2 & E2 & PO). injection E2 as Ems Emo. subst ms2' mo2x.
    unfold call_postA in PO. cbv beta in PO.
    ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & Ems2 & MI2 & ST2 & MF2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2).
    subst ms2.
    rewrite ?(unsigned_lit sp1) in ST2 by exact SP1R. rewrite ?(unsigned_lit sp1) in HP2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETR| exact RETE]).
    (* [comment removed for export] *)
    assert (HP0 : presA asegs R (lb_remove x (Lc ++ LB)) ((FB, 64) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [] mc ms).
    { eapply (presA_drop_freed asegs R HIA hc (Lc ++ LB) ((FB, 64) :: LF) (lb_remove x (Lc ++ LB)) [] x k mc mc ms sp1 HHc ltac:(apply in_or_app; left; exact HIN));
        [ intros b q Hb _; split; [eapply In_lb_remove; exact Hb| intros ->; exact (lb_remove_fst_neq _ _ _ ND Hb eq_refl)]
        | exact (proj1 DIMG) | exact (proj2 DIMG) | clear - ALO LOS SLO SP1 NS1 STKsi0 NRT; lia |].
      eapply presA_weaken with (W := [(wlo, whi)]) (LB := lb_remove x (Lc ++ LB)) (LF := (FB, 64) :: LF) (SP := sp1) (SSP := arl_stklo R) (TOP := hstkhi asegs R HIA hc);
        [ eapply (presA_of_munch asegs R) with (CS := hcs asegs R HIA hc);
            [ exact (hcs_ok asegs R HIA hc)
            | apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact (hm_blocks_cs asegs R HIA hc _ _ _ HHc x k ltac:(apply in_or_app; left; apply in_or_app; left; exact HIN))| clear - HWlo; lia| clear - HWlo HWhi; lia]| apply Forall_nil]
            | intros c Hc; eapply (cshd_hcs asegs R HIA hc (Lc ++ LB) ((FB, 64) :: LF) mc (arl_stklo R) c HHc ltac:(clear; lia));
              destruct Hc as [Hs|[(b & Hb & Hx)|Hr]]; [left; exact Hs| right; left; exists b; split; [eapply In_lb_remove; exact Hb| exact Hx]| right; right; exact Hr]
            | exact MU | exact WM ]
        | intros b Hb; exact Hb | intros b Hb; exact Hb | clear; lia | clear; lia | clear; lia
        | intros q Hq; cbn [outside] in Hq |- *; clear - Hq HWlo HWhi; lia ]. }
    pose proof (presA_trans asegs R _ _ _ _ _ _ _ _ _ HP0 HP2) as HP.
    assert (G2 : gvA FB sp1 W (PHIa + AVOL_CALL) (FFRa + fr_charge (d + 1)) w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc (lb_remove x Lc) m2 mo2 h2).
    { eapply (gvA_free R HIA) with (STKsi := STKsi) (Lc := Lc) (mc := mc) (moc := moc) (hc := hc) (x := x) (slo := slo) (d := d) (lo := lo) (W := W) (PHIa := PHIa) (FFRa := FFRa);
        first [ exact D0 | exact MI2 | exact ST2 | exact HP | exact HT2 | exact HS2 | exact HF2 | exact HK2 | exact HCS2 | exact HV2 | exact HFR2 | exact HH2
              | exact (mo_frame_trans _ _ _ MF1 MF2) | sec_hyps
              | lazymatch goal with |- In x (map fst Lc) => apply (in_map fst) in HIN; exact HIN end
              | eassumption
              | match goal with |- ?g => idtac "FREEST-GVA-LEFT:" g end ]. }
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo2) _ _ _ (conj HK2 (mo_frame_refl mo2))).
    eapply K; [exact G2| exact HP].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0140@D34536527705.259D5706805702.259 D67864004949.259L10444971817.1  L11316827680.3  L14014062319.235L14486843009.1  L16888294652.234L20658934102.1  L23011543279.235L23011543279.248L23187461660.4  L24381013773.18 L24425350392.277L27111942217.1  L31162548699.6  L31437355831.10 L32759717734.18 L35666023782.12 L37657122610.7  L38308634325.0  L39124586203.12 L39231752993.0  L39332637397.0  L39782001492.6  L40228640085.0  L42927756920.1  L43390267627.11 L44354377350.4  L45756604495.248L45924629402.5  L4689685756.234 L5457211416.1   L55516972878.9  L56874985056.8  L5731133105.1   L57647670710.9  L59308631400.1  L59308633593.1  L59310680273.3  L60098763854.6  L6393052521.235 L66771781187.2  L7575642888.1   Q1113788111.243 Q1113788111.273 Q11801279589.259Q14480193773.255Q14492448884.242Q22090054029.243Q22090054029.273Q23405925126.242Q29402318989.243Q3741646287.243 Q45082815691.243Q45095277549.242Q49698585326.257Q50773819496.272Q50775916550.242Q5455387083.243 Q5455387083.273 Q5455472244.255 Q5466023555.272 Q5468120813.242 Q56910164340.242Q5704530886.258 Q61272698277.256Q67865953109.25800000101902A02G02O03H03K05805;06406m07?07f07g07k08?08d09J09f0:@0:A0:i0:j0:k0;D0;E0;J0<20<?0=80=H0?50?80?Y0@40@70@X0@\0@`0A20A<0B>0BI0BL0Bo0CR0DD0Dg0EJ0G;0Hl0IO0K@0Kc0LF0Li0MU0N80N[0O>0Oa0PD0Pg0QJ0Qm0R_0SJ0T<FS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB2ns2rr1a2FB3sp13sgc3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB2ns2rr1a2FB3sp13sgc3SZC2HB5Ha_st5Hl_stS4PHIaS1d4FFRaS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB2ns2rr1a2FB3sp13sgc3SZCS1aS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS2ns2rr1a2FB3sp13sgc3SP13SZC3ALO3ACV3SPR2F04HPOS4ACE'S1aS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB2ns2rr1a2FB3sp13sgc3SZCS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB2ns2rr1a2FB3sp13sgc3SZCS2ns4PHIa4PHIx3LPXS1R3HIA5STKsi1h2sp3SIG2lo4SGLO3SLO1q2HqFS2PPS1d2ns4FFRa4FFRx3LFXS1R3HIA1h2ns3ns22r24PHIa3BUD4PHIx3LPXS1R3HIA5STKsi1h2sp2PP2lo4PPLO3SLO1q2HqS1R3HIA5STKsi1h2sp2lo3TOP2HTS1R3HIA1h4rest2rr4PHIa3BUDSS1R3HIA1h1d2ns3ns22r24FFRa4BUDF4FFRx3LFXSSS2ns3ns22r24PHIa4PHIx3LPXSS3SIGS1R3HIA1h1d2ns2rr4FFRa4BUDF3Dnn4FFRx3LFXS1d4rest4FFRaS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB2ns2rr1a2FB3sp13sgc3SZCS1R3ax23HP22C21HS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS2ns2rr1a2FB3sp13sgc3SP13SZC3ALO3ACV3SPR2F04HPOS4ACE'S1aS1R3HIA1h2ns2rr4PHIa3BUD4PHIx3LPXS1d2ns3ns22r24FFRa4FFRx3LFXS1aS1R3HIA1h1d4rest2rr4FFRa4BUDF3DnnS2KIS2KZS3ax22KZ3HP22n12KIS1R2lo3LOSS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB2ns2rr1a2FB3sp13sgc3SZC5inext2IBS4rest4PHIaS1aS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZCS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZCS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZCS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZCS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS2ns2rr1a2FB3sp13sgc3SP14SP1M3SZC3ALO3ACV3SPR2F03HAL4HPOSS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS2ns2rr1a2FB3sp13sgc3ALO3ACV3SPR3HAL4HPOS3SP14SP1M3SZC2F0S1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZCS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS2ns2rr1a2FB3sp13sgc3SP14SP1M3SZC3ALO3ACV3SPR2F03HAL4HPOSS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZCS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZCS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZCS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZC2HB5Ha_stS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZCS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZCS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZCS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZCS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZCS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZCS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZCS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZCS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc4HPOS3SZC2HBS1R5STKsi2LF2bs3LFB2ns2rr1a3sgc3SZC2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND FREE STKsi NRT LFB PP0 CWP PPLO BIN SG0 CWS SGLO DA0 CRDA DALO SLOS SLOL SLO TOP SPA TPV LOS"] Lemma CL2 : forall (sg : list (Z * list Z)) (a : Z) (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p : Z) (sgc : list cell) mc moc hc
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v s6v s7v s8v s11v : word),
    sg <> [] -> signer_chain asegs mc (sbl sg ++ LB) a sg ->
    gvA FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc (sbl sg) mc moc hc ->
    havol asegs R HIA h + PHIa + Z.of_nat (length (signer_blocks sg)) * AVOL_CALL <= AVOL_MAX ->
    hfr asegs R HIA h + FFRa + Z.of_nat (length (signer_blocks sg)) * fr_charge (d + 1) <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    (forall mc' moc' hc' (y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 s5' s6' s7' s8' s11' : word),
        gvA FB sp1 X0 (PHIa + Z.of_nat (length (signer_blocks sg)) * AVOL_CALL) (FFRa + Z.of_nat (length (signer_blocks sg)) * fr_charge (d + 1))
            w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc [] mc' moc' hc' ->
        aevtS asegs POST
          (mkCfg (MS (mkR (Z_to_bv 64 0x98e04) (Z_to_bv 64 sp1) gp tp y0 y1 y2 sp (Z_to_bv 64 sp1) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                          (Z_to_bv 64 FB) s4v s7' s5' s6' (Z_to_bv 64 (al_sb AL)) s8' (Z_to_bv 64 FB) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) s11' y3 y4 y5 y6)
                     F (Z_to_bv 64 0x98e0c) fc None mc' (seg_rom asegs)) moc')) ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 FB) s4v s7v (Z_to_bv 64 a) s6v (Z_to_bv 64 (al_sb AL)) s8v (Z_to_bv 64 FB) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) s11v t3 t4 t5 t6)
                 F (Z_to_bv 64 0x98d88) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros sg. induction sg as [|[a0' ns] rr IH];
      intros a FB sp1 PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc mc moc hc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v s6v s7v s8v s11v
             HNE HSC D BUD BUDF UW K; [congruence|].
    pose proof D as D0. gvA_open D. rt_facts. walk_prep. pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as Dnn.
    destruct (signer_chain_uncons asegs _ _ _ _ _ _ HSC) as (<- & HIN & HAL & HPOS & inext & nxt & j & HNODE & HNC & HSC').
    pose proof (HMND _ _ _ _ HHc) as NDL2. cbn [sbl] in NDL2. rewrite !map_app, map_fst_SNAME in NDL2. cbn [map fst] in NDL2. rewrite <- !app_assoc in NDL2.
    destruct (nodup4 _ _ _ _ NDL2) as (ND1 & ND2 & ND3 & ND4).
    pose proof (blocks_below_hm R HIA hc _ _ mc _ HHc ltac:(intros b Hb; exact Hb)) as BBc.
    destruct (BBc _ HIN) as [_ ACE']. cbn [fst snd] in ACE'. unfold SIGNER_SIZE in ACE'.
    pose proof (hm_aobj_block asegs R HIA hc _ _ mc a SIGNER_SIZE HHc HIN) as OA. unfold SIGNER_SIZE in OA.
    (* [comment removed for export] *)
    pose proof HNODE as HNODE'. unfold signer_cells in HNODE'.
    change (rw_cells asegs mc a ([CB 80 (sj0 j)] ++ [C8 (Z_to_bv 64 inext)] ++ [C1 (sj_merged j); CB 7 (sj1 j); CB 96 (sj2 j); C8 (Z_to_bv 64 nxt)])) in HNODE'.
    destruct (rw_cells_split3 asegs mc a _ _ _ HNODE') as (_ & CIN & CR3). cbn [cells_size csize Nat.add length] in CIN, CR3.
    replace (a + Z.of_nat 80) with (a + 80) in CIN by (clear; lia).
    change (rw_cells asegs mc (a + Z.of_nat 80 + Z.of_nat 8) ([C1 (sj_merged j); CB 7 (sj1 j); CB 96 (sj2 j)] ++ [C8 (Z_to_bv 64 nxt)] ++ [])) in CR3.
    destruct (rw_cells_split3 asegs mc _ _ _ _ CR3) as (_ & CNX & _). cbn [cells_size csize Nat.add length] in CNX.
    replace (a + Z.of_nat 80 + Z.of_nat 8 + Z.of_nat 104) with (a + 192) in CNX by (clear; lia). clear CR3 HNODE'.
    pose proof (chain_addr_range asegs _ _ _ _ _ _ _ HNC) as IB.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    clear CNX.
    (* [comment removed for export] *)
    assert (AT54 : forall mX moX hX PHIx FFRx (iw : word) (y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 y7 s7x : word),
      gvA FB sp1 X0 PHIx FFRx w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc (sbl rr ++ [(a, SIGNER_SIZE)]) mX moX hX ->
      signer_chain asegs mX ((sbl rr ++ [(a, SIGNER_SIZE)]) ++ LB) nxt rr ->
      rw_cells asegs mX (a + 80) [C8 iw] ->
      PHIx <= PHIa + Z.of_nat (length ns) * AVOL_CALL -> FFRx <= FFRa + Z.of_nat (length ns) * fr_charge (d + 1) ->
      aevtS asegs POST
        (mkCfg (MS (mkR y0 (Z_to_bv 64 sp1) gp tp y1 y2 ya0 sp (Z_to_bv 64 sp1) ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3
                        (Z_to_bv 64 FB) s4v s7x (Z_to_bv 64 a) (Z_to_bv 64 (a + 80)) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 nxt) (Z_to_bv 64 FB) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
                        (Z_to_bv 64 (Z.shiftr (a + 80) 3 + al_sb AL)) y4 y5 y6 y7)
                   F (Z_to_bv 64 0x98df0) fc None mX (seg_rom asegs)) moX)).
    { intros mX moX hX PHIx FFRx iw y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 y7 s7x G HSCr CINx LPX LFX.
      clear HHc HKc MFc HTc HSc HFc HCSc HVc HFRc PRES SP1 SP1M F64 FRSH CFB FHD G4 FSH SAVE RSL STb STlo PPc Hpc CSG SZC DAc BYc OPP OSG ODA OBUF MIc SSc LAWS KINV HNODE OA CIN.
      clear CSOKc HT CFBc SCS03c SCS SCSc OPPc OSGc ODAc CRP CRS CRDg APP APSG F0 F1 F2 F3 STKH WL WCS WCP CWSc CWPc.
      pose proof G as G0. gvA_open G. walk_prep.
      (* [comment removed for export] *)
      assert (HINx : In (a, SIGNER_SIZE) ((sbl rr ++ [(a, SIGNER_SIZE)]) ++ LB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
      pose proof (hm_aobj_block asegs R HIA hX _ _ mX a SIGNER_SIZE HHc HINx) as OAx. unfold SIGNER_SIZE in OAx.
      pose proof (blocks_below_hm R HIA hX _ _ mX _ HHc ltac:(intros b Hb; exact Hb)) as BBx.
      destruct (BBx _ HINx) as [_ ACEx]. cbn [fst snd] in ACEx. unfold SIGNER_SIZE in ACEx.
      lazymatch type of HHc with HM _ _ _ _ ?LBx ?LFx _ =>
        assert (INW : @In blk (a, 200) (@app blk LBx (fdata LFx))) by (apply in_or_app; left; exact HINx) end.
      pose proof (HMND _ _ _ _ HHc) as NDX.
      apply (aevtA_enter asegs (KF asegs R HIA hX moX) _ _ _ (conj HKc (mo_frame_refl moX))).
      pose proof (AIh_laws asegs R HIA hX) as LAWSx. pose proof (KF_kinv asegs R HIA hX moX) as KINVx.
      (* [comment removed for export] *)
      zstep. zstep.
      (* [comment removed for export] *)
      clear PRES FHD G4 FSH SAVE RSL STb PPc CSG DAc BYc OPP OSG ODA OBUF SSc OPPc OSGc ODAc.
      pose proof (munch_refl [(a + 80, a + 88)] mX) as MU. pose proof (wmono_refl asegs mX) as WM.
      (* [comment removed for export] *)
      zstep.
      clear OAx.
      zstep. zstep.
      replace (Z_to_bv 64 431228) with (Z_to_bv 64 (arl_free R)) by (rewrite FREE; reflexivity).
      assert (TST1 : forall q, bv_unsigned sp <= q < hstkhi asegs R HIA h -> outside X0 q).
      { intros q Hq. cbn [outside]. split; [clear - Hq PPLO LOS SLO NS1 STKsi0 NRT; lia| split; [clear - Hq SGLO LOS SLO NS1 STKsi0 NRT; lia| exact I]]. }
      assert (TST2 : hfr asegs R HIA h + FFRx + fr_charge (d + 1) <= FR_MAX).
      { budlia ltac:(clear - BUDF LFX Dnn). }
      assert (TST3 : havol asegs R HIA h + PHIx + AVOL_CALL <= AVOL_MAX).
      { budlia ltac:(clear - BUD LPX). }
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?msx _) =>
      eapply free_stepA_st with (hc := hX) (moc := moX) (mc := mX) (ms := msx) (Lc := sbl rr ++ [(a, SIGNER_SIZE)]) (x := a) (k := SIGNER_SIZE) (wlo := a + 80) (whi := a + 88)
                                (PHIa := PHIx) (FFRa := FFRx) (W := X0);
        first [ exact G0 | exact UW | exact TST1 | exact TST2 | exact TST3 | exact MU | exact WM | exact NDX
              | lazymatch goal with
                | |- In (a, SIGNER_SIZE) _ => apply in_or_app; right; left; reflexivity
                | |- a <= a + 80 => clear; lia
                | |- a + 88 <= a + SIGNER_SIZE => unfold SIGNER_SIZE; clear; lia
                | |- 0 <= _ < 2 ^ 64 => clear; lia
                | |- _ mod 2 = 0 => reflexivity
                | |- forall m1 mo1 h1, _ => idtac
                end
              | eassumption
              | match goal with |- ?g => idtac "CL2-FREEST-LEFT:" g end ]
      end.
      cbv beta. intros m1 mo1 h1 z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 G1 HPf.
      pose proof NDX as ND0. rewrite !map_app in ND0. cbn [map fst] in ND0. apply NoDup_app_inv_l in ND0.
      assert (HINL : In a (map fst (sbl rr ++ [(a, SIGNER_SIZE)]))) by (rewrite map_app; apply in_or_app; right; left; reflexivity).
      assert (ELc : lb_remove a (sbl rr ++ [(a, SIGNER_SIZE)]) = sbl rr).
      { change (sbl rr ++ [(a, SIGNER_SIZE)]) with (sbl rr ++ (a, SIGNER_SIZE) :: []). rewrite lb_remove_mid; [apply app_nil_r|].
        intros Hx. apply (NoDup_app_notin_l _ _ a ND0); [left; reflexivity| exact Hx]. }
      rewrite ELc in G1.
      assert (HSC1 : signer_chain asegs m1 (sbl rr ++ LB) nxt rr).
      { replace (sbl rr ++ LB) with (lb_remove a ((sbl rr ++ [(a, SIGNER_SIZE)]) ++ LB)) by (rewrite lb_remove_app_l by exact HINL; rewrite ELc; reflexivity).
        eapply (signer_chain_presx0 R mX m1 _ _ sp1 []); [exact HSCr| | | intros b _ _; exact I].
        - intros b Hb. apply In_lb_remove_keep'; [eapply (signer_blocks_in asegs); [exact HSCr| exact Hb]|].
          cbn. intros E. apply (NoDup_app_notin_l _ _ (fst b) ND0); [left; symmetry; exact E|].
          pose proof (sbl_perm rr) as PB. apply (in_map fst). eapply Permutation_in; [apply Permutation_sym; exact PB| exact Hb].
        - eapply heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HPf)| intros b Hb; apply in_or_app; left; exact Hb| apply Z.le_refl| intros x Hx; exact Hx]. }
      clear HPf G0 HSCr MU WM.
      pose proof G1 as G1'. ddestruct G1' as (HH1 & HK1 & MF1 & HT1 & HS1 & _).
      pose proof (AIh_laws asegs R HIA h1) as LAWS1. pose proof (KF_kinv asegs R HIA h1 mo1) as KINV1.
      (* [comment removed for export] *)
      zstep.
      zstep. if_cases KZ; zify_cond KZ.
      - (* [comment removed for export] *)
        destruct rr as [|[ax2 ns2] r2]; [exfalso; cbn in HSC1; subst nxt; clear - KZ; cbv in KZ; lia|].
        intros moq [HKq MFq].
        eapply (IH nxt FB sp1); [congruence| exact HSC1| eapply gvA_mo; [exact G1| exact HKq| exact MFq]| | | exact UW|].
        + budlia ltac:(clear - BUD LPX).
        + budlia ltac:(clear - BUDF LFX Dnn).
        + intros mc' moc' hc' q0 q1 q2 qa0 qa1 qa2 qa3 qa4 qa5 qa6 qa7 q3 q4 q5 q6 s5' s6' s7' s8' s11' G'. eapply K.
          eapply gvA_bud; [exact G'| budlia ltac:(clear - LPX)| budlia ltac:(clear - LFX Dnn)].
      - (* [comment removed for export] *)
        destruct rr as [|[ax2 ns2] r2].
        2:{ exfalso. pose proof (signer_chain_uncons asegs _ _ _ _ _ _ HSC1) as (-> & HINx2 & _ & HP2 & _).
            pose proof (blocks_below_hm R HIA h1 _ _ m1 _ HH1 ltac:(intros b Hb; exact Hb)) as BB1. destruct (BB1 _ HINx2) as [_ C2]. cbn [fst snd] in C2.
            kz2 KZ HP2 C2. clear - KZ HP2. lia. }
        cbn [sbl app] in G1.
        intros moq [HKq MFq]. eapply K.
        eapply gvA_bud; [eapply gvA_mo; [exact G1| exact HKq| exact MFq]
                        | budlia ltac:(clear - LPX)
                        | budlia ltac:(clear - LFX Dnn)]. }
    (* [comment removed for export] *)
    zstep. if_cases KI; zify_cond KI.
    2:{ (* [comment removed for export] *)
        destruct ns as [|n1 rest]; [exfalso; cbn in HNC; subst inext; clear - KI; cbv in KI; lia|].
        cbn [sbl] in D0, HSC', HNC.
        intros moq [HKq MFq].
        eapply (CL3 R HIA) with (STKsi := STKsi) (nodes := n1 :: rest) (A := sbl rr) (B := [(a, SIGNER_SIZE)])
                                (RR := fun mX Lx => signer_chain asegs mX (Lx ++ LB) nxt rr /\ In (a, SIGNER_SIZE) Lx /\ rw_cells asegs mX (a + 80) [C8 (Z_to_bv 64 inext)])
                                (PHIa := PHIa) (FFRa := FFRa) (slo := slo) (d := d) (lo := lo) (hc := hc) (mc := mc) (moc := moq);
          first [ exact UW | sec_hyps
                | lazymatch goal with
                  | |- _ :: _ <> [] => congruence
                  | |- name_chain _ _ _ _ _ _ => first [exact HNC | rewrite <- app_assoc in HNC; exact HNC | rewrite app_assoc in HNC; exact HNC | rewrite <- app_assoc; exact HNC | rewrite app_assoc; exact HNC]
                  | |- List.NoDup (n1 :: rest) => apply List.NoDup_rev in ND1; rewrite rev_involutive in ND1; exact ND1
                  | |- forall x, In x _ -> ~ In x (map fst (sbl rr)) => intros x Hx; apply ND2; apply (proj1 (in_rev _ _)); exact Hx
                  | |- _ /\ In (a, SIGNER_SIZE) _ /\ _ => split; [first [exact HSC' | rewrite <- app_assoc in HSC'; exact HSC' | rewrite app_assoc in HSC'; exact HSC' | rewrite <- app_assoc; exact HSC' | rewrite app_assoc; exact HSC']| split; [apply in_or_app; right; apply in_or_app; right; left; reflexivity| exact CIN]]
                  | |- havol _ _ _ _ + _ + _ <= _ => budlia ltac:(clear - BUD)
                  | |- hfr _ _ _ _ + _ + _ <= _ => budlia ltac:(clear - BUDF Dnn)
                  | |- forall mX mY hX rest' x, _ => idtac
                  | |- forall mc' moc' hc', _ => idtac
                  end
                | (lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signers_C.gvA] => idtac end end;
                   eapply gvA_mo; [first [exact D0 | rewrite <- app_assoc in D0; exact D0 | rewrite app_assoc in D0; exact D0 | rewrite <- app_assoc; exact D0 | rewrite app_assoc; exact D0]| exact HKq| exact MFq])
                | match goal with |- ?g => idtac "CL2-CL3-LEFT:" g end ].
        + (* [comment removed for export] *)
          intros mX mY hX rest' x [R1 [R2 R3]] Hx Hnr HHx HSx HPx.
          pose proof (HMND _ _ _ _ HHx) as NDx. cbn [sbl] in NDx. rewrite !map_app, map_fst_SNAME in NDx. cbn [map fst] in NDx. rewrite <- !app_assoc in NDx.
          destruct (nodup4 _ _ _ _ NDx) as (NX1 & NX2 & NX3 & NX4).
          assert (XA : ~ In x (map fst (sbl rr))) by (apply NX2; apply (proj1 (in_rev _ _)); left; reflexivity).
          assert (NA : x <> a) by (intros ->; apply (NX3 a); [apply (proj1 (in_rev _ _)); left; reflexivity| left; reflexivity]).
          rewrite <- (rm_node (sbl rr) [(a, SIGNER_SIZE)] x rest' XA Hnr).
          split; [| split; [apply In_lb_remove_keep'; [exact R2| cbn; intros E; exact (NA (eq_sym E))]|]].
          2:{ (* [comment removed for export] *)
              eapply (presA_rw_cells asegs R); [exact HPx| exact R3| | exact I].
              cbn [cells_size csize Nat.add]. eapply client_range_block;
                [ apply in_or_app; left; apply In_lb_remove_keep'; [apply in_or_app; left; exact R2| cbn; intros E; exact (NA (eq_sym E))]
                | clear; lia | unfold SIGNER_SIZE; clear; lia ]. }
          rewrite <- (lb_remove_app_l x _ LB (in_node _ _ x rest')).
          eapply (signer_chain_presx0 R mX mY _ _ sp1 []); [exact R1| | | intros b _ _; exact I].
          * intros b Hb. apply In_lb_remove_keep'; [eapply (signer_blocks_in asegs); [exact R1| exact Hb]|].
            cbn. intros E. apply XA. rewrite <- E. apply (in_map fst). eapply Permutation_in; [apply Permutation_sym; apply sbl_perm| exact Hb].
          * eapply heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HPx)| intros b Hb; apply in_or_app; left; exact Hb| apply Z.le_refl| intros q Hq; exact Hq].
        + intros mc' moc' hc' q0 q1 q2 qa0 qa1 qa2 qa3 qa4 qa5 qa6 qa7 q3 q4 q5 q6 s7' G' [R1 [R2 R3]].
          eapply AT54; [first [exact G' | rewrite <- app_assoc in G'; exact G' | rewrite app_assoc in G'; exact G']| first [exact R1 | rewrite <- app_assoc in R1; exact R1 | rewrite app_assoc in R1; exact R1]| exact R3| budlia ltac:(clear)| budlia ltac:(clear - Dnn)]. }
    (* [comment removed for export] *)
    destruct ns as [|n1 rest].
    2:{ exfalso. pose proof (chain_uncons asegs _ _ _ _ _ _ _ _ HNC) as (-> & HIN2 & _ & HP2 & _).
        destruct (BBc _ HIN2) as [_ C2]. cbn [fst snd] in C2.
        kz2 KI HP2 C2. clear - KI HP2. lia. }
    cbn [sbl rev SNAME map app] in D0, HSC'. cbn in HNC. subst inext.
    intros moq [HKq MFq].
    eapply AT54; [ eapply gvA_mo; [first [exact D0 | rewrite <- app_assoc in D0; exact D0 | rewrite app_assoc in D0; exact D0]| exact HKq| exact MFq]
                 | first [exact HSC' | rewrite <- app_assoc in HSC'; exact HSC' | rewrite app_assoc in HSC'; exact HSC'] | exact CIN | budlia ltac:(clear)| budlia ltac:(clear - Dnn)].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
