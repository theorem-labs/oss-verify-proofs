(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_pkcs7_signers.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag
     A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt A_pkcs7_signers_A A_pkcs7_signers_B A_pkcs7_signers_C A_pkcs7_signers_D A_pkcs7_signers_E A_pkcs7_signers_F A_pkcs7_signers_G A_pkcs7_signers_H.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "01P0@D12949562016.230D25662884252.230D3953997537.231 D60109196847.230D60189065437.231K12838370724.230K28788825731.230K44164039966.230K49341710523.230K49936266399.230L12126572370.2  L12790317110.2  L12850865746.2  L15756354262.7  L1685717371.0   L17925432628.4  L2036051503.2   L25764509176.217L26457316758.5  L27111942217.1  L28632618922.2  L28776318325.2  L32280122272.2  L3290553667.219 L330814680.4    L35666023782.12 L37232046390.2  L38259954321.2  L38308634325.0  L39332637397.0  L40228640085.0  L42927756920.1  L44166924249.3  L44168742175.3  L46890498175.6  L49326776262.2  L49936279650.2  L50790731766.12 L57698627611.2  L59308633593.1  L59310680273.3  L60098763854.6  L8274779545.7   P12115299733.231P12795822833.231P2042605906.230 P28627113325.231P32294539623.230P37243319281.231P38261788758.231P44164039966.231P57713046236.231Q12949562016.230Q12951513248.229Q21157640433.228Q21914785289.227Q23258654747.230Q25660900252.229Q25662884252.230Q26713403899.227Q27458512306.231Q27940668300.227Q28337929679.228Q28465177121.228Q32681824661.231Q33929113211.227Q33933185373.226Q3419689062.231 Q3421936230.230 Q35294347281.227Q37149073081.231Q38167875878.231Q39180574961.231Q42219631003.228Q42439443119.230Q42439443119.231Q47451547014.227Q4823565255.227 Q4825674107.228 Q49531895963.227Q5265442331.229 Q52984985372.226Q55415036769.231Q56854244147.231Q57228775306.230Q57230951818.231Q59198584676.227Q59865321072.230Q59865321072.231Q60572573391.227Q64592257022.226Q64683667846.230Q64683667846.231Q66337817851.228Q67183863355.227Q7528279444.227 00001@02P04H05_07U08[09a0:g0;k0=10=20=30=40=B0=C0=M0=N0=O0=_0=c0=d0=e0=f0?N0?Y0@50@60@70@80@90@:0@?0@@0@A0@]0@^0@_0A:0A;0A?0AK0AU0B30CK0D`0Em0GK0H`0J:0KX0M80NA0O?0P=0Q50R60R70S50T30T40UI0VJ0W90Wk0Wl0X[0YJ0ZV0[b0\[0^30^40_L0a@0bG0cR0dA0e00e_0gS0hK0i:0jC0jD0kX0ll0m[0m\0m]0nL0o;10M11c11d12Z13SS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB2sg2FB3sp16inext05snext3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB2sg2FB3sp16inext05snext3sjh3SZC2HB5Ha_st5Hl_stS1R3HIA5STKsi1h2LF2sp2PP3SIG4DALG2bs3LFB3PP03SG03DA03TOP2sg2FB3sp16inext05snext3sjh2hc3HTc3SP13SZC3SPR2F02HB5Ha_st5Hl_stS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3LOS2sg2FB3sp16inext05snext3sjh3SZC2HB5Ha_st5Hl_stS1R3NS15STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS2sg2FB3sp16inext05snext3sjh3SP13SZC3SPR2F02HB5Ha_st5Hl_stS1R5STKsi2LF3SIG2bs3LFB2sg2FB6inext05snext3sjh3SZC4APSG2HB5Ha_st5Hl_stS1R5STKsi2LF3SIG2bs3LFB2sg2FB6inext05snext3sjh3SZC4APSG2HB5Ha_st5Hl_stS1R5STKsi2LF3BUF3SIG2bs3LFB3DSB2sg6inext05snext3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2PP3SIG2bs3LFB2D12sg6inext05snext3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF3SIG4DALG2bs3LFB2D32sg6inext05snext3sjh3SZC2HB5Ha_st5Hl_stFFFS1R2lo3LOS3ALOSS2PP1B1k1HFFS1R3a1'3HP22C21HS2PPFFFS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG04SGLO3DA03SLO3SPH2sg2FB3sp16inext05snext3sjh3SP13SZC3SPR2F0S3SIG1B1k1HS1R3HIA5STKsi1h2sp2lo3TOP2HTFFSSSS3SIGFFS5PHIsi5CNTsi1P3END4PHIa3PHIFFS1R3NS15STKsi2sp2lo3SLO3LOSFS2KZS3a1'2KZ3HP2S1R2lo3LOSS5FFRsi5CNTsi1P3END1d4FFRa3FFRS1R5STKsi2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO2sg3sp16inext05snext3sjh3SP13SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp3SIG2lo2bs3LFB4SGLO3SLO2sg3sp16inext05snext3sjh3SP13SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp3SIG2lo2bs3LFB4SGLO3SLO2sg6inext05snext3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp3SIG2lo2bs3LFB3SLO3LOS2sg2FB3sp16inext05snext3sjh3SP13SZC3ALO2F12HB5Ha_st5Hl_stS1R5STKsi2LF2sp3SIG2lo2bs3LFB4SGLO3SLO2sg3sp16inext05snext3sjh3SP13SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp3SIG4DALG2lo2bs3LFB4DALO3SLO2sg3sp16inext05snext3sjh3SP13SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp3SIG2lo2bs3LFB3SLO3LOS2sg2FB3sp16inext05snext3sjh3SP13SZC3ALO2F12HB5Ha_st5Hl_stS1R5STKsi2LF2sp3BUF3SIG2lo2bs3LFB3SLO3LOS2sg3sp16inext05snext3sjh3SP13SZC3ALO3BCE2HB5Ha_st5Hl_stS1R5STKsi2LF2sp3SIG2bs3LFB2sg3sp16inext05snext3sjh3SP13SZC2HB5Ha_st5Hl_stS1R5STKsi2LF3SIG2bs3LFB2sg6inext05snext3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF3SIG2bs3LFB2sg6inext05snext3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF3SIG2bs3LFB2sg6inext05snext3sjh3SZC2HB5Ha_stS1R3NS15STKsi2LF2sp2lo2bs3LFB3SLO2sg3sp16inext05snext3sjh3SP13SZCFS1R5STKsi2LF3SIG2bs3LFB2sg6inext05snext3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF3SIG2bs3LFB2sg6inext05snext3sjh3SZC2HB5Ha_st5Hl_stFS1R5STKsi2LF2sp3SIG2lo2bs3LFB4SGLO3SLO2sg3sp16inext05snext3sjh3SP13SZC2HB5Ha_st5Hl_stS1R3NS15STKsi2LF2sp2lo2bs3LFB3SLO2sg3sp16inext05snext3sjh3SP13SZCS1R5STKsi2LF3SIG2bs3LFB2sg6inext05snext3sjh3SZCS1R5STKsi2LF2bs3LFB2sg3sp16inext05snext3sjh3SZC2HBFS1R5STKsi2LF3SIG2bs3LFB2sg6inext05snext3sjh3SZCS1R5STKsi2LF3SIG2bs3LFB2sg6inext05snext3sjh3SZCS1R5STKsi2LF2sp3SIG2lo2bs3LFB2sg3sp16inext05snext3sjh3SP13SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp3SIG2lo2bs3LFB2sg3sp16inext05snext3sjh3SP13SZC2HB5Ha_st5Hl_stS1R5STKsi2LF2sp2lo2bs3LFB2sg3sp16inext05snext3sjh3SP13SZCS1R5STKsi2LF2sp2PP3SIG2lo2bs3LFB4PPLO3SLO2sg3sp16inext05snext3sjh3SP13SZC2HB5Ha_st5Hl_stFS1R5STKsi2LF2sp3SIG2lo2bs3LFB3SLO3LOS2sg3sp16inext05snext3sjh3SP13SZC3ALO2HB5Ha_st5Hl_stS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03ALS3SG03DA03SLO3LOS2sg2FB3sp16inext05snext3sjh3SP14SP1M3SZC3ALO3ACV3SPR2F0S1R5STKsi2LF3SIG3slo2bs3LFB4SLOS2sg6inext05snext3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF3SIG3slo2bs3LFB4SLOS2sg3sp16inext05snext3sjh3SZC2HB5Ha_st5Hl_stS1R5STKsi2LF3SIG2bs3LFB2sg6inext05snext3sjh3SZCS1R5STKsi2LF3SIG2bs3LFB2sg6inext05snext3sjh3SZCS1R5STKsi2LF3SIG2bs3LFB2sg6inext05snext3sjh3SZCS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03ALS3SG03DA03SLO3LOS2sg2FB3sp16inext05snext3sjh3SP14SP1M3SZC3ALO3ACV3SPR2F0S1R5STKsi2LF2bs3LFB2sg3sp16inext05snext3sjh3SZC2HB5Ha_stS1R5STKsi2LF3SIG2bs3LFB2sg6inext05snext3sjh3SZCS1R5STKsi2LF2sp3SIG2bs3LFB2sg3sp16inext05snext3sjh3SP13SZC2HB5Ha_st5Hl_stFS1R3NS15STKsi2LF2sp3SIG2lo2bs3LFB3SLO2sg3sp16inext05snext3sjh3SP13SZC2HB5Ha_st5Hl_stS1R3NS15STKsi2LF2sp3SIG2lo2bs3LFB3SLO2sg3sp16inext05snext3sjh3SP13SZC2HB5Ha_st5Hl_stS1R5STKsi2LF3SIG2bs3LFB2sg6inext05snext3sjh3SZCFFS1R5STKsi2LF3SIG2bs3LFB2sg6inext05snext3sjh3SZCS1R5STKsi2LF3SIG2bs3LFB2sg6inext05snext3sjh3SZCS1R3HIA5STKsi1h2LF2sp3SIG3slo2bs3LFB3TOP2sg6inext05snext3sjh3SZC2HT2HB5Ha_st5Hl_stS1R3HIA5STKsi1h2LF2sp3SIG3slo2bs3LFB3TOP2sg3sp16inext05snext3sjh3SZC2HT2HB5Ha_st5Hl_stFS1R5STKsi2LF3SIG2bs3LFB3SG02sg6inext05snext3sjh3SZC2HBS1R5STKsi2LF2sp2lo2bs3LFB2sg3sp16inext05snext3sjh3SP13SZC". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND FREE STKsi CNTsi_mono LFB PP0 CWP PPLO BIN B1 B2 B3 DPB ALS SG0 CWS SGLO DSB DA0 CRDA DALO D1 D2 D3 SLOS SLOL SLO TOP SPA SPH TPV LOS"] Lemma CL_50 : forall (sg : list (Z * list Z)) (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p inext0 snext : Z) (sjh : signer_junk) mc moc hc (r : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s7v s11v : word),
    gvA FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p (signer_cells inext0 snext sjh) (sbl sg) mc moc hc ->
    signer_chain asegs mc (sbl sg ++ LB) snext sg ->
    havol asegs R HIA h + PHIa + Z.of_nat (length (signer_blocks sg)) * AVOL_CALL <= AVOL_MAX ->
    hfr asegs R HIA h + FFRa + Z.of_nat (length (signer_blocks sg)) * fr_charge (d + 1) <= FR_MAX ->
    PHIa + Z.of_nat (length (signer_blocks sg)) * AVOL_CALL <= PHIs PHIsi CNTsi NB ->
    FFRa + Z.of_nat (length (signer_blocks sg)) * fr_charge (d + 1) <= FFRs FFRsi CNTsi NB d ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    -2^31 < r < 2^31 ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 FB) (Z_to_bv 64 r) (Z_to_bv 64 (Z.shiftr (SIG + 80) 3 + al_sb AL)) s5v s7v (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 SIG) (Z_to_bv 64 FB)
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) s11v t3 t4 t5 t6)
                 F (Z_to_bv 64 0x98d58) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s11v. intros D HSC BUD BUDF PHI FFR UW Hr. pose proof D as D0. gvA_open D. rt_facts. walk_prep. pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as Dnn.
    pose proof (signer_chain_nonnull asegs _ _ _ _ HSC) as HNN.
    unfold signer_cells in CSG. cbn [sj0 sj_merged sj1 sj2] in CSG.
    (* [comment removed for export] *)
    pose proof (presW_init_at R HIA hc _ _ (sbl sg ++ LB) LF mc (bv_unsigned sp) (bv_unsigned sp) X0 h HHc
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSc HSc ltac:(clear - LOS SLO NS1 STKsi0 NRT; lia)) as PRESq.
    assert (WLq : wlow R (sbl sg ++ LB) LF) by (split; [exact (proj2 (proj2 (proj2 PRESq)))| apply (art_data_lo asegs R HIA)]).
    assert (WCSq : wcover R (sbl sg ++ LB) LF (bv_unsigned sp) X0 SIG 200) by (apply wcover_inside; cbn [inside]; right; left; clear; lia).
    (* [comment removed for export] *)
    pose proof (blocks_below_hm R HIA hc _ _ mc _ HHc ltac:(intros b Hb; exact Hb)) as BB1.
    destruct (BB1 (BUF, n) ltac:(apply in_or_app; right; exact BIN)) as [_ BCE]. cbn [fst snd] in BCE. clear BB1.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    (* [comment removed for export] *)
    assert (HSC1 : signer_chain asegs m1 (sbl sg ++ LB) snext sg).
    { lazymatch goal with PQ : presW _ _ _ hc (sbl sg ++ LB) LF _ _ X0 mc m1 |- _ =>
        eapply (signer_chain_presx0 R mc m1 _ _ (bv_unsigned sp) X0);
          [ exact HSC | intros b Hb; eapply (signer_blocks_in asegs); [exact HSC| exact Hb]
          | eapply heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA _ _ _ _ _ _ _ _ PQ))| intros b Hb; apply in_or_app; left; exact Hb| apply Z.le_refl| intros x Hx; exact Hx]
          | ] end.
      intros [B k] Hb Hk. cbn [fst snd] in Hk |- *.
      assert (HbL : In (B, k) (sbl sg)) by (eapply Permutation_in; [apply Permutation_sym; apply sbl_perm| exact Hb]).
      split; [| split; [| exact I]].
      - pose proof (obj_apart_new R HIA hc (sbl sg) LB LF ((FB, 64) :: LF) _ lo (htop asegs R HIA h) PP 8 B k DIMG HHc ltac:(intros fb Hfb; right; exact Hfb) CWP ltac:(clear - ALO LOS; lia) ltac:(clear; lia) HbL Hk).
        clear - H. lia.
      - pose proof (obj_apart_new R HIA hc (sbl sg) LB LF ((FB, 64) :: LF) _ lo (htop asegs R HIA h) SIG 200 B k DIMG HHc ltac:(intros fb Hfb; right; exact Hfb) CWS ltac:(clear - ALO LOS; lia) ltac:(clear; lia) HbL Hk).
        clear - H. lia. }
    clear HSC PRESq WLq WCSq.
    (* [comment removed for export] *)
    zstep. if_cases KZ; zify_cond KZ.
    - destruct sg as [|[a1' ns1] r1].
      2:{ exfalso. destruct (signer_chain_uncons asegs _ _ _ _ _ _ HSC1) as (-> & HINx & _ & HP2 & _).
          lazymatch goal with HH : HM _ _ _ hc _ _ m1 |- _ => pose proof (blocks_below_hm R HIA hc _ _ m1 _ HH ltac:(intros b Hb; exact Hb)) as BB1 end.
          destruct (BB1 _ HINx) as [_ C2]. cbn [fst snd] in C2. kz2 KZ HP2 C2. clear - KZ HP2. lia. }
      cbn in HSC1. subst snext.
      intros moq [HKq MFq].
      eapply (CL_END R HIA) with (STKsi := STKsi) (slo := slo) (d := d) (lo := lo) (hc := hc) (mc := m1) (moc := moq) (PHIa := PHIa) (FFRa := FFRa);
        first [ sec_hyps
              | lazymatch goal with
                | |- PHIa <= _ => budlia ltac:(clear - PHI)
                | |- FFRa <= _ => budlia ltac:(clear - FFR)
                | |- _ < r < _ => exact Hr
                end
              | (lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signers_C.gvA] => idtac end end;
                 eapply gvA_mo; [| exact HKq| exact MFq];
                 split; [cbn [sbl app] in HHc |- *; exact HHc|]; split; [exact HKc|]; split; [exact MFc|]; split; [exact HTc|]; split; [exact HSc|]; split; [exact HFc|]; split; [exact HCSc|];
                 split; [exact HVc|]; split; [exact HFRc|]; split; [eassumption|];
                 repeat match goal with |- _ /\ _ => split end;
                 first [ eassumption | reflexivity
                       | lazymatch goal with |- rw_cells _ m1 SIG _ => lazymatch goal with CE : rw_cells _ m1 SIG _ |- _ => unfold signer_cells; cbn [sj0 sj_merged sj1 sj2 app]; exact CE end end
                       | match goal with H : ?a <= ?x <= ?b |- ?a' <= ?x' => first [exact (proj1 H) | exact (proj2 H)] end
                       | match goal with |- ?g => idtac "GVA50b-LEFT:" g end ])
              | match goal with |- ?g => idtac "CL50-END2-LEFT:" g end ].
    - (* [comment removed for export] *)
      destruct sg as [|[a1' ns1] r1]; [exfalso; cbn in HSC1; subst snext; clear - KZ; cbv in KZ; lia|].
      intros moq [HKq MFq].
      eapply (CL2 R HIA) with (STKsi := STKsi) (sg := (a1', ns1) :: r1) (PHIa := PHIa) (FFRa := FFRa) (hc := hc) (mc := m1) (moc := moq) (slo := slo) (d := d) (lo := lo);
        first [ exact UW | sec_hyps
              | lazymatch goal with
                | |- _ :: _ <> [] => congruence
                | |- signer_chain _ _ _ _ _ => exact HSC1
                | |- havol _ _ _ _ + _ + _ <= _ => exact BUD
                | |- hfr _ _ _ _ + _ + _ <= _ => exact BUDF
                | |- forall mc' moc' hc', _ => idtac
                end
              | (lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signers_C.gvA] => idtac end end;
                 eapply gvA_mo; [| exact HKq| exact MFq];
                 split; [exact HHc|]; split; [exact HKc|]; split; [exact MFc|]; split; [exact HTc|]; split; [exact HSc|]; split; [exact HFc|]; split; [exact HCSc|];
                 split; [exact HVc|]; split; [exact HFRc|]; split; [eassumption|];
                 repeat match goal with |- _ /\ _ => split end;
                 first [ eassumption | reflexivity
                       | lazymatch goal with |- rw_cells _ m1 SIG _ => lazymatch goal with CE : rw_cells _ m1 SIG _ |- _ => unfold signer_cells; cbn [sj0 sj_merged sj1 sj2 app]; exact CE end end
                       | match goal with H : ?a <= ?x <= ?b |- ?a' <= ?x' => first [exact (proj1 H) | exact (proj2 H)] end
                       | match goal with |- ?g => idtac "GVA50-LEFT:" g end ])
              | match goal with |- ?g => idtac "CL50-CL2-LEFT:" g end ].
      intros mc' moc' hc' y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 s5' s6' s7' s8' s11' G'.
      eapply (CL_END R HIA) with (STKsi := STKsi) (slo := slo) (d := d) (lo := lo); first [exact G' | exact PHI | exact FFR | exact Hr | sec_hyps | eassumption | match goal with |- ?g => idtac "CL50-END1-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00P0@L11217303772.219L11939080819.220L12447270864.8  L21810362649.9  L27111942217.1  L31437125803.7  L35666023782.12 L37657122610.6  L37657122610.7  L38308634325.0  L39124720301.9  L39332637397.0  L40228640085.0  L42927756920.1  L48167901769.219L55748456706.1  L57647670710.8  L57647670710.9  L59308631400.1  L59310680273.3  L60098763854.6  L6839932503.7   L7589134086.10  Q26713403899.228Q27942899219.227Q33929113211.228Q33933185373.227Q35288190350.227Q49531895963.228Q52984985372.227Q60572573391.228Q64592257022.22700001_02g03K03l04004J04f05;05U05V06306406506:07E07J07b08C08G08R08\09;09a09b0:j0;`0<V0=V0?Q0@G0A=0B3S1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG04SGLO3DA03SLO3SPH2FB3sp16inext05snext3sjh6names02sg3SP13SZC3SPR2F0S1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp16inext05snext3sjh6names02sg3SZCS5PHIsi5CNTsi1P3END4PHIa4rest2sg3PHIS5FFRsi5CNTsi1P3END1d4FFRa2sg3FFRS2PPS1R3HIA1h4PHIa4rest2sg3BUDS1R3HIA5STKsi1h2sp2lo3TOP2HTS1R3HIA1h4PHIa2sg3BUDS1R3HIA1h4PHIa4rest2sg3BUDSS1R3HIA1h1d4FFRa4rest2sg4BUDFSSS3SIGS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp16inext05snext3sjh6names02sg3SZC2IBS3SIGS1R3HIA1h1d4FFRa2sg4BUDFS1R3HIA1h1d4FFRa4rest2sg4BUDF3DnnS2KIS2n12KI3HP2S1R2lo3LOSS5PHIsi5CNTsi1P3END4PHIa2sg3PHIS5FFRsi5CNTsi1P3END1d4FFRa4rest2sg3FFRFS1R3NS15STKsi2LF2sp2lo2bs3LFB3SLO3sp16inext05snext3sjh6names02sg3SP13SZCS1R5STKsi2LF3SIG2bs3LFB6inext05snext3sjh6names02sg3SZCS1R5STKsi2LF3SIG2bs3LFB6inext05snext3sjh6names02sg3SZCS1R5STKsi2LF2sp2lo2bs3LFB3sp16inext05snext3sjh6names02sg3SP13SZCS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03ALS3SG03DA03SLO3LOS2FB3sp16inext05snext3sjh6names02sg3SP14SP1M3SZC3ALO3ACV3SPR2F0S1R5STKsi2LF3SIG2bs3LFB6inext05snext3sjh6names02sg3SZCS1R5STKsi2LF3SIG2bs3LFB6inext05snext3sjh6names02sg3SZCS1R5STKsi2LF3SIG2bs3LFB6inext05snext3sjh6names02sg3SZC". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND FREE STKsi CNTsi_mono LFB PP0 CWP PPLO BIN B1 B2 B3 DPB ALS SG0 CWS SGLO DSB DA0 CRDA DALO D1 D2 D3 SLOS SLOL SLO TOP SPA SPH TPV LOS"] Lemma CLEAN : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k16 k24 : word) (j32 : list byte)
      (p inext0 snext : Z) (sjh : signer_junk) (names0 : list Z) (sg : list (Z * list Z)) mc moc hc (r : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s7v s8v s11v : word),
    gvA FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 k0 (Z_to_bv 64 SIG) k16 k24 j32 p (signer_cells inext0 snext sjh) (sbl sg ++ SNAME (rev names0)) mc moc hc ->
    name_chain asegs (fun _ => True) mc ((sbl sg ++ SNAME (rev names0)) ++ LB) inext0 names0 ->
    signer_chain asegs mc ((sbl sg ++ SNAME (rev names0)) ++ LB) snext sg ->
    havol asegs R HIA h + PHIa + (Z.of_nat (length names0) + Z.of_nat (length (signer_blocks sg))) * AVOL_CALL <= AVOL_MAX ->
    hfr asegs R HIA h + FFRa + (Z.of_nat (length names0) + Z.of_nat (length (signer_blocks sg))) * fr_charge (d + 1) <= FR_MAX ->
    PHIa + (Z.of_nat (length names0) + Z.of_nat (length (signer_blocks sg))) * AVOL_CALL <= PHIs PHIsi CNTsi NB ->
    FFRa + (Z.of_nat (length names0) + Z.of_nat (length (signer_blocks sg))) * fr_charge (d + 1) <= FFRs FFRsi CNTsi NB d ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    -2^31 < r < 2^31 ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 FB) (Z_to_bv 64 r) s6v s5v s7v (Z_to_bv 64 (al_sb AL)) s8v (Z_to_bv 64 FB)
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) s11v t3 t4 t5 t6)
                 F (Z_to_bv 64 0x98d04) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s11v. intros D HNC HSC BUD BUDF PHI FFR UW Hr. pose proof D as D0. gvA_open D. rt_facts. walk_prep. pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as Dnn.
    pose proof (chain_addr_range asegs _ _ _ _ _ _ _ HNC) as IB.
    pose proof (HMND _ _ _ _ HHc) as NDL2. rewrite !map_app, map_fst_SNAME in NDL2. rewrite <- !app_assoc in NDL2.
    pose proof CSG as CSG'. unfold signer_cells in CSG'. cbn [sj0 sj_merged sj1 sj2] in CSG'.
    change (rw_cells asegs mc SIG ([CB 80 (sj0 sjh)] ++ [C8 (Z_to_bv 64 inext0)] ++ [C1 (sj_merged sjh); CB 7 (sj1 sjh); CB 96 (sj2 sjh); C8 (Z_to_bv 64 snext)])) in CSG'.
    destruct (rw_cells_split3 asegs mc SIG _ _ _ CSG') as (_ & CIN & _). clear CSG'. cbn [cells_size csize Nat.add length] in CIN.
    replace (SIG + Z.of_nat 80) with (SIG + 80) in CIN by (clear; lia).
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    clear CIN.
    (* [comment removed for export] *)
    zstep. if_cases KI; zify_cond KI.
    - (* [comment removed for export] *)
      destruct names0 as [|n1 rest].
      2:{ exfalso. destruct (chain_uncons asegs _ _ _ _ _ _ _ _ HNC) as (-> & HIN2 & _ & HP2 & _).
          pose proof (blocks_below_hm R HIA hc _ _ mc _ HHc ltac:(intros b Hb; exact Hb)) as BB1. destruct (BB1 _ HIN2) as [_ C2]. cbn [fst snd] in C2.
          kz2 KI HP2 C2. clear - KI HP2. lia. }
      cbn [rev SNAME map] in D0, HSC. rewrite app_nil_r in D0, HSC. cbn in HNC. subst inext0.
      intros moq [HKq MFq].
      eapply (CL_50 sg FB sp1 PHIa FFRa); [eapply gvA_mo; [exact D0| exact HKq| exact MFq]| exact HSC| budlia ltac:(clear - BUD)| budlia ltac:(clear - BUDF Dnn)| budlia ltac:(clear - PHI)| budlia ltac:(clear - FFR Dnn)| exact UW| exact Hr].
    - destruct names0 as [|n1 rest]; [exfalso; cbn in HNC; subst inext0; clear - KI; cbv in KI; lia|].
      intros moq [HKq MFq].
      eapply (CL1 R HIA) with (STKsi := STKsi) (nodes := n1 :: rest) (A := sbl sg) (B := @nil blk)
                              (RR := fun mX Lx => signer_chain asegs mX (Lx ++ LB) snext sg)
                              (PHIa := PHIa) (FFRa := FFRa) (slo := slo) (d := d) (lo := lo) (hc := hc) (mc := mc) (moc := moq);
        first [ exact UW | sec_hyps
              | lazymatch goal with
                | |- _ :: _ <> [] => congruence
                | |- name_chain _ _ _ _ _ _ => rewrite app_nil_r; exact HNC
                | |- List.NoDup (n1 :: rest) => apply NoDup_app_inv_r in NDL2; apply NoDup_app_inv_l in NDL2; apply List.NoDup_rev in NDL2; rewrite rev_involutive in NDL2; exact NDL2
                | |- forall x, In x _ -> ~ In x (map fst (sbl sg)) => intros x Hx; apply (NoDup_app_notin_l _ _ x NDL2); apply in_or_app; left; apply (proj1 (in_rev _ _)); exact Hx
                | |- signer_chain _ _ _ _ _ => rewrite app_nil_r; exact HSC
                | |- havol _ _ _ _ + _ + _ <= _ => budlia ltac:(clear - BUD)
                | |- hfr _ _ _ _ + _ + _ <= _ => budlia ltac:(clear - BUDF Dnn)
                | |- forall mX mY hX rest' x, _ => idtac
                | |- forall mc' moc' hc', _ => idtac
                end
              | (lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signers_C.gvA] => idtac end end;
                 rewrite app_nil_r; eapply gvA_mo; [exact D0| exact HKq| exact MFq])
              | match goal with |- ?g => idtac "CLEAN-CL1-LEFT:" g end ].
      + intros mX mY hX rest' x R1 Hx Hnr HHx HSx HPx.
        pose proof (HMND _ _ _ _ HHx) as NDx. rewrite !map_app, map_fst_SNAME in NDx. rewrite <- !app_assoc in NDx.
        assert (XA : ~ In x (map fst (sbl sg))).
        { apply (NoDup_app_notin_l _ _ x NDx). apply in_or_app. left. apply (proj1 (in_rev _ _)). left. reflexivity. }
        rewrite <- (rm_node (sbl sg) [] x rest' XA Hnr). rewrite <- (lb_remove_app_l x _ LB (in_node _ _ x rest')).
        eapply (signer_chain_presx0 R mX mY _ _ sp1 []); [exact R1| | | intros b _ _; exact I].
        * intros b Hb. apply In_lb_remove_keep'; [eapply (signer_blocks_in asegs); [exact R1| exact Hb]|].
          cbn. intros E. apply XA. rewrite <- E. apply (in_map fst). eapply Permutation_in; [apply Permutation_sym; apply sbl_perm| exact Hb].
        * eapply heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HPx)| intros b Hb; apply in_or_app; left; exact Hb| apply Z.le_refl| intros q Hq; exact Hq].
      + intros mc' moc' hc' y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 s6' G' R'.
        rewrite app_nil_r in G', R'.
        eapply (CL_50 sg FB sp1); [exact G'| exact R'| budlia ltac:(clear - BUD)| budlia ltac:(clear - BUDF Dnn)| budlia ltac:(clear - PHI)| budlia ltac:(clear - FFR Dnn)| exact UW| exact Hr].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
