(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_pkcs7_signer.     (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag
     A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt A_pkcs7_signer_A A_pkcs7_signer_B A_pkcs7_signer_C
     A_pkcs7_signers_A A_pkcs7_signers_C A_pkcs7_signers_D A_pkcs7_signers_G.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw TacA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import LiaOrcFF5. (* [comment removed for export] *)
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
Definition A_WFREE : Z := 0x68f08.                (* [comment removed for export] *) (* [comment removed for export] *)

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
  Hypothesis NAM0 : 0 <= arl_need_amem R.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55857805827.20000003S1R". (* [comment removed for export] *)
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition STKsg : Z := 176 + Z.max (Z.max STKn 4208) (Z.max (240 + arl_need_amem R) (Z.max (112 + arl_need_smalloc R) (Z.max (arl_need_rt R) (arl_need_bcmp R)))).

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L38885538412.800000BS1R4STKn2sp2lo3SLO". (* [comment removed for export] *)
  Let SLOq : lo <= bv_unsigned sp - A_pkcs7_signers_A.STKs R STKn.
  Proof. unfold A_pkcs7_signers_A.STKs. unfold STKsg in SLO. clear - SLO NS1 NAM0 STKn0. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac sec_hyps :=
    first [ exact IMG | exact UARG | exact SM0 | exact NS1 | exact DIMG | exact HMND | exact CALLOC | exact FREE | exact STKn0 | exact NAM0
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
    lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signers_C.gvA] => idtac end end;
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

  (* [comment removed for export] *)
  Definition SC (pre : list cell) (j48 : list byte) (inext : Z) (mg : byte) (pad7 : list byte) (post : list cell) : list cell :=
    pre ++ [CB 48 j48; C8 (Z_to_bv 64 inext); C1 mg; CB 7 pad7] ++ post ++ [C8 (Z_to_bv 64 0)].

  #[using="Type"] Lemma SC_size : forall pre j48 inext mg pad7 post, cells_size pre = 32%nat -> cells_size post = 96%nat -> cells_size (SC pre j48 inext mg pad7 post) = 200%nat.
  Proof. clear - HIA. intros. unfold SC. rewrite !cells_size_app, H, H0. reflexivity. Qed.

  #[using="Type"] Lemma SC_signerA : forall mX pre j48 inext mg pad7 post,
    rw_cells asegs mX SIG (SC pre j48 inext mg pad7 post) -> cells_size pre = 32%nat -> cells_size post = 96%nat ->
    rw_cells asegs mX SIG (signer_cells inext 0 (SGJ (cells_bytes pre ++ j48) mg pad7 (cells_bytes post))).
  Proof.
    clear - HIA. intros mX pre j48 inext mg pad7 post H SZ1 SZ2. unfold SC in H.
    replace (pre ++ [CB 48 j48; C8 (Z_to_bv 64 inext); C1 mg; CB 7 pad7] ++ post ++ [C8 (Z_to_bv 64 0)])
      with ((pre ++ [CB 48 j48]) ++ [C8 (Z_to_bv 64 inext); C1 mg; CB 7 pad7] ++ (post ++ [C8 (Z_to_bv 64 0)])) in H
      by (repeat rewrite <- app_assoc; reflexivity).
    destruct (rw_cells_split3 asegs mX SIG _ _ _ H) as (H1 & H2 & H3).
    destruct (proj1 (rw_cells_app asegs mX _ post [C8 (Z_to_bv 64 0)]) H3) as [H3a H3b].
    apply (rw_cells_blob asegs) in H1. apply (rw_cells_blob asegs) in H3a.
    rewrite cells_size_app, SZ1 in H1. cbn [cells_size csize Nat.add] in H1. rewrite cells_bytes_app in H1. cbn [cells_bytes cbytes] in H1. rewrite app_nil_r in H1.
    rewrite ?cells_size_app, ?SZ1, ?SZ2 in H2. rewrite ?cells_size_app, ?SZ1, ?SZ2 in H3a. rewrite ?cells_size_app, ?SZ1, ?SZ2 in H3b.
    cbn [cells_size csize Nat.add] in H2, H3a, H3b.
    unfold signer_cells. cbn [sj0 sj_merged sj1 sj2].
    change [CB 80 (cells_bytes pre ++ j48); C8 (Z_to_bv 64 inext); C1 mg; CB 7 pad7; CB 96 (cells_bytes post); C8 (Z_to_bv 64 0)]
      with ([CB 80 (cells_bytes pre ++ j48)] ++ [C8 (Z_to_bv 64 inext); C1 mg; CB 7 pad7] ++ ([CB 96 (cells_bytes post)] ++ [C8 (Z_to_bv 64 0)])).
    apply rw_cells_join3; [exact H1| cbn [cells_size csize Nat.add]; exact H2|].
    cbn [cells_size csize Nat.add]. apply rw_cells_app. split; [exact H3a| cbn [cells_size csize Nat.add]; exact H3b].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00h0@D2472962947.228 D60109196847.228D60868265762.228K12226132804.228K21870859916.228K22945712379.228K44164039966.228K4812443226.228 L11939080819.217L12220097593.2  L12257830543.1  L14447004729.2  L1685717371.0   L21866712442.2  L22941438733.2  L27111942217.1  L34254337233.2  L35050589957.4  L35666023782.13 L38308634325.0  L39332637397.0  L40228640085.0  L42927756920.1  L43957762635.2  L44168742175.3  L45111486027.1  L4812559015.2   L49493397620.5  L55748456706.1  L59314955108.3  L60098763854.6  L60378851463.215L63195017561.1  L6867749463.217 L7736277618.2   L8074271943.2   P14461423358.228P7750690063.228 Q10349087299.225Q11801279589.228Q13436634747.228Q2470748547.227 Q2472962947.228 Q26713403899.225Q33929113211.225Q33931153912.224Q42439443119.228Q49531895963.225Q49698585326.226Q52995143609.224Q59865321072.228Q60572573391.225Q60868265762.228Q60870544674.227Q64577118043.224Q64683667846.22800001802G03O04K05I06G07E08C09<09=09B09C09D09E09F09J09K09\0:70:80:90::0:?0:G0:H0:M0:N0:X0:]0:g0;10;20;70<00<10<90=F0>K0?90?o0@00@f0A\0A]0BD0Bk0Cj0E[0FK0G20G30GZ0HP0IF0Im0K7S1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13pre4post3SZ13SZ22HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3LOS2FB3sp13pre4post3SZ13SZ22HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13pre4post3SZ13SZ22HB5Ha_st5Hl_stS1R4STKn2LF2PP3SIG2bs3LFB2D13pre4post3SZ13SZ22HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB2FB3pre4post3SZ13SZ24APSG2HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB2FB3pre4post3SZ13SZ24APSG2HB5Ha_st5Hl_stS1R4STKn2LF3BUF3SIG2bs3LFB3DSB3pre4post3SZ13SZ22HB5Ha_st5Hl_stS1R4STKn2LF3SIG4DALG2bs3LFB2D33pre4post3SZ13SZ22HB5Ha_st5Hl_stS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13pre4post3SZ13SZ2FS3SIGFSFFS2PPSS4CNTn1P3END4CS0'S1R3HIA4STKn1h2sp2lo3TOP2HTSSSS3SIGS2ar3HarFS3SIGFS1P3END2B2S3SIGS2ar3Har1ES1R2lo3LOSFS3SIGS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13pre4post3SZ13SZ2FS2ar3HarS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3sp13pre4post3SP13SZ13SZ22HB5Ha_st5Hl_stS1R4STKn2LF2sp3SIG2lo2bs3LFB4SGLO3SLO3pre4post3SZ13SZ22HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB3SG03pre4post3SZ13SZ22HBS1R4STKn2LF3SIG2bs3LFB3pre4post3SZ13SZ22HB5Ha_st5Hl_stFS1R4STKn2LF3SIG2bs3LFB3pre4post3SZ13SZ22HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB3pre4post3SZ13SZ22HB5Ha_st5Hl_stFS1R4STKn2LF3SIG2bs3LFB3pre4post3SZ13SZ2S1R4STKn2LF3SIG2bs3LFB3pre4post3SZ13SZ2S1R4STKn2LF3SIG3slo2bs3LFB4SLOS3pre4post3SZ13SZ22HB5Ha_st5Hl_stS1R4STKn4NAM02LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03ALS3SG03DA03SLO3LOS2FB3sp13pre4post3SP14SP1M3SZ13SZ23ALO3ACV3SPR2F0S1R4STKn2LF3SIG2bs3LFB3pre4post3SZ13SZ22HB5Ha_stS1R4STKn2LF3SIG2bs3LFB3pre4post3SZ13SZ2FS1R4STKn2LF3SIG2bs3LFB3pre4post3SZ13SZ2S1R4STKn2LF3SIG2bs3LFB3pre4post3SZ13SZ22HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB3pre4post3SZ13SZ22HB5Ha_st5Hl_stS1R4STKn2LF3SIG2bs3LFB3pre4post3SZ13SZ2S1R3HIA4STKn1h2LF2sp3SIG3slo2bs3LFB3TOP3pre4post3SZ13SZ22HT2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG NS1 STKn CNTn_mono NAM0 LFB PP0 CWP PPLO B2 ALS SG0 CWS SGLO DSB DA0 DALO D1 D3 SLOS SLOL SLO TOP SPH LOS"] Lemma AF0 : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p : Z) (pre : list cell) (j48 : list byte) (inext : Z) (mg : byte) (pad7 : list byte) (post : list cell) mc moc hc (ar : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s7v : word),
    gvA FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p (SC pre j48 inext mg pad7 post) [] mc moc hc ->
    cells_size pre = 32%nat -> cells_size post = 96%nat ->
    PHIa <= PHIsi NB -> FFRa <= FFRsi NB d -> -0x8000 < ar <= 0 ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 FB) (Z_to_bv 64 (SIG + 80)) (Z_to_bv 64 (Z.shiftr (SIG + 80) 3 + al_sb AL)) s5v s6v s7v (Z_to_bv 64 ar) (Z_to_bv 64 FB)
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 (al_sb AL)) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x988b8) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s7v. intros D SZ1 SZ2 PHI FFR Har. pose proof D as D0. gvA_open D. rt_facts. walk_prep.
    pose proof (CNTn_mono 0 NB ltac:(clear - B1 B2; lia)) as CS0'.
    (* [comment removed for export] *)
    pose proof CSG as CSG0. unfold SC in CSG.
    lazymatch type of CSG with rw_cells _ _ _ ?cs =>
      replace cs with ((pre ++ [CB 48 j48]) ++ [C8 (Z_to_bv 64 inext)] ++ ([C1 mg; CB 7 pad7] ++ post ++ [C8 (Z_to_bv 64 0)])) in CSG
        by (repeat rewrite <- app_assoc; reflexivity) end.
    destruct (rw_cells_split3 asegs mc SIG _ _ _ CSG) as (CS1 & CNX & CS3). clear CSG.
    rewrite !cells_size_app, SZ1 in CNX, CS3. cbn [cells_size csize Nat.add] in CNX, CS3.
    replace (SIG + Z.of_nat 80) with (SIG + 80) in CNX by (clear; lia). replace (SIG + Z.of_nat 80 + Z.of_nat 8) with (SIG + 88) in CS3 by (clear; lia).
    pose proof (conj CS1 (conj CS3 I)) as CBOX. clear CS1 CS3 SZC CSG0.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => pose proof (munch_refl [(SIG + 80, SIG + 88)] mx) as MU1; pose proof (wmono_refl asegs mx) as WM1 end.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m1 end.
    ddestruct CBOX as (CS1 & CS3 & _).
    pose proof (rw_cells_transport asegs _ mc m1 _ _ CS1 MU1 WM1 ltac:(rewrite cells_size_app, SZ1; cbn [cells_size csize Nat.add disjoint_from]; split; [clear; lia| exact I])) as CS1'.
    pose proof (rw_cells_transport asegs _ mc m1 _ _ CS3 MU1 WM1 ltac:(rewrite !cells_size_app, SZ2; cbn [cells_size csize Nat.add disjoint_from]; split; [clear; lia| exact I])) as CS3'.
    assert (CSj : rw_cells asegs m1 SIG (SC pre j48 0 mg pad7 post)).
    { unfold SC. replace (pre ++ [CB 48 j48; C8 (Z_to_bv 64 0); C1 mg; CB 7 pad7] ++ post ++ [C8 (Z_to_bv 64 0)])
        with ((pre ++ [CB 48 j48]) ++ [C8 (Z_to_bv 64 0)] ++ ([C1 mg; CB 7 pad7] ++ post ++ [C8 (Z_to_bv 64 0)])) by (repeat rewrite <- app_assoc; reflexivity).
      apply rw_cells_join3; [exact CS1'| rewrite cells_size_app, SZ1; cbn [cells_size csize Nat.add]; replace (SIG + Z.of_nat 80) with (SIG + 80) by (clear; lia); assumption
        | rewrite cells_size_app, SZ1; cbn [cells_size csize Nat.add]; replace (SIG + Z.of_nat 80 + Z.of_nat 8) with (SIG + 88) by (clear; lia); exact CS3']. }
    pose proof (SC_signerA m1 _ _ _ _ _ _ CSj SZ1 SZ2) as CSS.
    clear CS1 CS3 CS1' CS3' MU1 WM1.
    match goal with H : rw_cells _ m1 (SIG + 80) _ |- _ => clear H end.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    first [ rewrite (swrap32_land_errsum ar 18446744073709529472) by (clear - Har; lia)
          | match goal with |- ?g => idtac "AF0-ADDW-FORM:" g end ].
    intros moq [HKq MFq].
    eapply (ret_walkS R HIA) with (STKn := STKn) (nodes := []) (inext := 0) (PHIa := PHIa) (FFRa := FFRa) (slo := slo) (d := d) (lo := lo) (hc := hc) (mc := m1) (moc := moq) (W := X0) (p := p)
                                 (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
      first [ sec_hyps | exact PHI | exact FFR
            | lazymatch goal with
              | |- name_chain _ _ _ _ _ _ => cbn; reflexivity
              | |- List.NoDup [] => constructor
              | |- forall x, In x [] -> _ => intros xq []
              | |- Z.of_nat (length []) <= _ => unfold A_pkcs7_signer_C.CNTsi; cbn [length Z.of_nat]; clear - CS0'; lia
              | |- forall x, outside _ x -> outside _ x => intros xq Hxq; exact Hxq
              | |- _ < _ <= 0 => clear - Har; lia
              | |- _ = 0 -> _ => intros E; exfalso; clear - E Har; lia
              | |- _ <> 0 -> _ => intros; reflexivity
              end
            | (lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signers_C.gvA] => idtac end end;
               eapply gvA_mo; [| exact HKq| exact MFq]; gvA_fin HKc MFc (mo_frame_refl moc))
            | match goal with |- ?g => idtac "AF0-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0@L11535534713.5  L12112729974.19 L17905066372.8  L17991598320.212L21376922785.0  L30776801053.19 L31437125803.6  L35497567916.5  L39124720301.8  L40228640085.0  L44984951545.4  L46425563800.232L47028033785.213L5367532848.1   L59308633593.1  L59310680273.3  L5966946069.6   L65005791566.3  L68237972690.2  Q25019582490.217Q29612090062.217Q32352309670.218Q47700973017.218Q47713708799.217Q61338516829.21800000A00g01E02S02T03;03P03Q03i03j04504605;05A05E05P05g05o06806g07V09U0:D0;30;bS1R2n23ACV3HP22C2S1R3HIA4STKn1h2sp2PP2lo4PPLO3SLO2aq2HaS1R3HIA1h1d4rest4FFRa4BUDF3DnnS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB4rest3cur2FB3sp13sgc3SZC4HPOS3pre2nx4post3NBDSS1R3HIA4STKn1h2sp3SIG2lo4SGLO3SLO2aq2HaS1R3HIA1h2r24PHIa3BUDSS1R3HIA1h1d2r24FFRa4BUDFSS1d2r24FFRaFS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB4rest3cur2FB3sp13sgc3SZC3pre2nx4postS4PHIaS2KZS2n22KZ3HP2S1R3HIA1h4rest4PHIa3BUDS1d4FFRaS2r24PHIaS1R4STKn2LF2bs3LFB4rest3cur3sgc3SZC3pre2nx4postS1R4STKn2LF2bs3LFB4rest3cur3sgc3SZC3pre2nx4postS1R4STKn4NAM02LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS4rest3cur2FB3sp13sgc3SP14SP1M3SZC3ALO3ACV3SPR3HAL4HPOS3pre2nx4postS1R4STKn2LF2bs3LFB4rest3cur3sgc3SZC3pre2nx4postS1R4STKn2LF2bs3LFB4rest3cur3sgc3SZC3pre2nx4postS1R4STKn2LF2bs3LFB4rest3cur3sgc3SZC3pre2nx4post". (* [comment removed for export] *)
  #[using="IMG NS1 HMND FREE STKn NAM0 LFB PP0 CWP PPLO BIN SG0 CWS SGLO DA0 CRDA DALO SLOS SLOL SLO TOP SPA TPV LOS SLOq"] Lemma loopN : forall (nodes : list Z) (cur : Z) (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p : Z) (sgc : list cell) mc moc hc
      (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s4v s5v s6v s7v s8v : word),
    nodes <> [] -> name_chain asegs (fun _ => True) mc (SNAME (rev nodes) ++ LB) cur nodes -> List.NoDup nodes ->
    gvA FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc (SNAME (rev nodes)) mc moc hc ->
    havol asegs R HIA h + PHIa + Z.of_nat (length nodes) * AVOL_CALL <= AVOL_MAX ->
    hfr asegs R HIA h + FFRa + Z.of_nat (length nodes) * fr_charge (d + 1) <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    (forall mc' moc' hc' (y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 s5' : word),
        gvA FB sp1 X0 (PHIa + Z.of_nat (length nodes) * AVOL_CALL) (FFRa + Z.of_nat (length nodes) * fr_charge (d + 1)) w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc [] mc' moc' hc' ->
        aevtS asegs POST
          (mkCfg (MS (mkR (Z_to_bv 64 0x988b0) (Z_to_bv 64 sp1) gp tp y0 y1 y2 sp (Z_to_bv 64 sp1) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                          (Z_to_bv 64 FB) s3v s4v s5' s6v s7v s8v (Z_to_bv 64 FB) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 (al_sb AL)) y3 y4 y5 y6)
                     F (Z_to_bv 64 0x988b8) fc None mc' (seg_rom asegs)) moc')) ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 cur) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 FB) s3v s4v s5v s6v s7v s8v (Z_to_bv 64 FB) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 (al_sb AL)) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x98894) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros nodes. induction nodes as [|n1 rest IH];
      intros cur FB sp1 PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc mc moc hc xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s4v s5v s6v s7v s8v
             HNE HC HNDn D BUD BUDF UW K; [congruence|].
    pose proof D as D0. gvA_open D. rt_facts.
    pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as Dnn.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT. rewrite HTc, HSc in HT.
    destruct (chain_uncons asegs _ _ _ _ _ _ _ _ HC) as (<- & HIN & HAL & HPOS & pre & nx & post & Hsz1 & Hsz2 & HNODE & _ & HNX0 & HC').
    unfold NAME_NEXT in HNX0, Hsz1. unfold NAME_SIZE in Hsz2, HIN.
    pose proof (rw_cells_bound _ _ _ _ HNODE) as NBD. rewrite Hsz2 in NBD.
    apply List.NoDup_cons_iff in HNDn. destruct HNDn as [Hn1 HNDr].
    pose proof (hm_aobj_block asegs R HIA hc _ _ mc cur 64 HHc HIN) as OCUR.
    pose proof (blocks_below_hm R HIA hc _ _ mc _ HHc ltac:(intros b Hb; exact Hb)) as BBc.
    destruct (BBc _ HIN) as [_ CCE]. cbn [fst snd] in CCE.
    (* [comment removed for export] *)
    ddestruct (rw_cells_split3 asegs mc cur pre [C8 (Z_to_bv 64 nx)] post ltac:(exact HNODE)) as (_ & CNX & _). rewrite Hsz1 in CNX.
    clear HNODE.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 429832) with (Z_to_bv 64 (arl_free R)) by (rewrite FREE; reflexivity).
    clear CNX.
    eapply (free_stepA R HIA) with (STKsi := STKn) (hc := hc) (moc := moc) (mc := mc) (Lc := SNAME (rev (cur :: rest))) (x := cur) (k := 64)
                                   (PHIa := PHIa) (FFRa := FFRa) (slo := slo) (d := d) (W := X0) (lo := lo)
                                   (h := h) (LB := LB) (LF := LF) (m := m) (mo0 := mo0) (PP := PP) (SIG := SIG) (DALG := DALG) (P := P) (END := END) (BUF := BUF) (bs := bs) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
      first [ exact D0 | exact UW | sec_hyps
            | lazymatch goal with
              | |- In (cur, 64) _ => cbn [rev]; rewrite SNAME_app; apply in_or_app; right; left; reflexivity
              | |- List.NoDup _ => exact (HMND _ _ _ _ HHc)
              | |- havol _ _ _ _ + _ + _ <= _ => cbn [length] in BUD; unfold AVOL_CALL in *; clear - BUD; lia
              | |- hfr _ _ _ _ + _ + _ <= _ => cbn [length] in BUDF; unfold fr_charge in *; clear - BUDF Dnn; lia
              | |- forall a, _ -> outside X0 a => intros aq Ha; cbn; split; [clear - Ha PPLO LOS SLO NS1 NAM0 STKn0 NRT; lia| split; [clear - Ha SGLO LOS SLO NS1 NAM0 STKn0 NRT; lia| exact I]]
              | |- 0 <= _ < 2 ^ 64 => clear; lia
              | |- _ mod 2 = 0 => reflexivity
              | |- forall m1 mo1 h1, _ => idtac
              end
            | match goal with |- ?g => idtac "LN-FREE-LEFT:" g end ].
    cbv beta. intros m1 mo1 h1 y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 G1 HPf.
    assert (HINL : In cur (map fst (SNAME (rev (cur :: rest))))) by (cbn [rev]; rewrite SNAME_app, map_app; apply in_or_app; right; left; reflexivity).
    pose proof (lb_remove_head_node cur rest [] Hn1) as ELc0. rewrite !app_nil_r in ELc0.
    lazymatch type of G1 with context [lb_remove ?x ?l] =>
      first [ replace (lb_remove x l) with (SNAME (rev rest)) in G1 by (symmetry; exact ELc0)
            | replace (lb_remove x l) with (SNAME (rev rest)) in G1 by (symmetry; etransitivity; [| exact ELc0]; reflexivity)
            | idtac "LBR-FORM" ] end.
    (* [comment removed for export] *)
    assert (HC1 : name_chain asegs (fun _ => True) m1 (SNAME (rev rest) ++ LB) nx rest).
    { rewrite <- (lb_remove_head_node cur rest LB Hn1).
      eapply (chain_presx asegs L _ _ _ mc m1 _ _ sp1 []);
        [ exact HC'
        | intros x Hx; apply In_lb_remove_keep'; [eapply (chain_nodes_in asegs); [exact HC'| exact Hx]| cbn; intros E; subst x; exact (Hn1 Hx)]
        | eapply heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HPf)| intros b Hb; apply in_or_app; left; exact Hb| apply Z.le_refl| intros x Hx; exact Hx]
        | unfold NAME_SIZE; clear; lia
        | intros x _; exact I ]. }
    clear HHc PRES STlo MIc SSc HPf D0 HC HC' OCUR.
    pose proof G1 as G1'. ddestruct G1' as (HH1 & HK1 & MF1 & HT1 & HS1 & _).
    pose proof (AIh_laws asegs R HIA h1) as LAWS1. pose proof (KF_kinv asegs R HIA h1 mo1) as KINV1.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases KZ; zify_cond KZ.
    - (* [comment removed for export] *)
      destruct rest as [|n2 r2]; [exfalso; cbn in HC1; subst nx; clear - KZ; cbv in KZ; lia|].
      intros moq [HKq MFq].
      eapply (IH nx FB sp1 (PHIa + AVOL_CALL) (FFRa + fr_charge (d + 1)) w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc m1 moq h1);
        [ congruence | exact HC1 | exact HNDr
        | eapply gvA_mo; [exact G1| exact HKq| exact MFq]
        | cbn [length] in BUD |- *; unfold AVOL_CALL in *; clear - BUD; lia
        | cbn [length] in BUDF |- *; unfold fr_charge in *; clear - BUDF Dnn; lia
        | exact UW | ].
      intros mc' moc' hc' z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 sk' G'.
      eapply K. eapply gvA_bud; [exact G'| cbn [length]; unfold AVOL_CALL; clear; lia| cbn [length]; unfold fr_charge; clear - Dnn; lia].
    - (* [comment removed for export] *)
      destruct rest as [|n2 r2].
      2:{ exfalso. pose proof (chain_uncons asegs _ _ _ _ _ _ _ _ HC1) as (-> & HIN2 & _ & HP2 & _).
          pose proof (blocks_below_hm R HIA h1 _ _ m1 _ HH1 ltac:(intros b Hb; exact Hb)) as BB1. destruct (BB1 _ HIN2) as [_ C2]. cbn [fst snd] in C2. unfold NAME_SIZE in C2.
          first [change 18446744073709551615 with (Z.ones 64) in KZ; rewrite Z.land_ones in KZ by (clear - HP2 C2 ACV; lia) | idtac].
          first [change (2 ^ 64) with 18446744073709551616 in KZ | change (2 ^ Z.of_N 64) with 18446744073709551616 in KZ | idtac].
          rewrite ?Z.mod_small in KZ by (clear - HP2 C2 ACV; lia). rewrite ?unsigned_lit in KZ by (clear - HP2 C2 ACV; lia).
          clear - KZ HP2; lia. }
      cbn in HC1. subst nx.
      intros moq [HKq MFq].
      eapply K.
      eapply gvA_bud; [eapply gvA_mo; [exact G1| exact HKq| exact MFq]| cbn [length]; unfold AVOL_CALL; clear; lia| cbn [length]; unfold fr_charge; clear - Dnn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00G0@L11217303772.223L11939080819.224L27111942217.1  L35666023782.13 L3760832063.8   L3761024346.9   L38308634325.0  L38723088065.6  L39332637397.0  L40228640085.0  L42927756920.1  L55748456706.1  L59308633593.1  L59310680273.3  L60098763854.6  L6393050616.223 Q26713403899.232Q33929113211.232Q33933185373.231Q49531895963.232Q52984985372.231Q60572573391.232Q64592257022.23100002103F03J03e04A04B04C04]04^04_04d04i04m05805B06Z06[07^08a0:n0<10=40>7S1R4STKn4NAM02LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG04SGLO3DA03SLO3SPH2FB3sp13pre3j485inext2mg4pad74post5nodes3SP13SZC3SZ13SZ23SPR2F0S1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13pre3j485inext2mg4pad74post5nodes3SZC3SZ13SZ2S2PPS1R3HIA4STKn1h2sp2lo3TOP2HTS4FFRn4CNTn1P3END1d4FFRa3FFRFSS4PHIn4CNTn1P3END4PHIa3PHISSS3SIGS3SIGS2KZS2n12KZ3HP2S1R2lo3LOSS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB2FB3sp13pre3j485inext2mg4pad74post5nodes3SZC3SZ13SZ22IBFS1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74post5nodes3SZC3SZ13SZ2S1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74post5nodes3SZC3SZ13SZ2S1R4STKn4NAM02LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03ALS3SG03DA03SLO3LOS2FB3sp13pre3j485inext2mg4pad74post5nodes3SP14SP1M3SZC3SZ13SZ23ALO3ACV3SPR2F0S1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74post5nodes3SZC3SZ13SZ2S1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74post5nodes3SZC3SZ13SZ2S1R4STKn2LF3SIG2bs3LFB3pre3j485inext2mg4pad74post5nodes3SZC3SZ13SZ2". (* [comment removed for export] *)
  #[using="IMG NS1 HMND FREE STKn CNTn_mono NAM0 LFB PP0 CWP PPLO BIN B2 ALS SG0 CWS SGLO DSB DA0 CRDA DALO D1 D3 SLOS SLOL SLO TOP SPA SPH TPV LOS SLOq"] Lemma OUT : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p : Z) (pre : list cell) (j48 : list byte) (inext : Z) (mg : byte) (pad7 : list byte) (post : list cell) (nodes : list Z) mc moc hc (ar : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v s5v s6v s7v : word),
    gvA FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p (SC pre j48 inext mg pad7 post) (SNAME (rev nodes)) mc moc hc ->
    cells_size pre = 32%nat -> cells_size post = 96%nat ->
    name_chain asegs (fun _ => True) mc (SNAME (rev nodes) ++ LB) inext nodes -> List.NoDup nodes ->
    havol asegs R HIA h + PHIa + Z.of_nat (length nodes) * AVOL_CALL <= AVOL_MAX ->
    hfr asegs R HIA h + FFRa + Z.of_nat (length nodes) * fr_charge (d + 1) <= FR_MAX ->
    PHIa + Z.of_nat (length nodes) * AVOL_CALL <= PHIsi NB -> FFRa + Z.of_nat (length nodes) * fr_charge (d + 1) <= FFRsi NB d ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    -0x8000 < ar <= 0 ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 FB) (Z_to_bv 64 SIG) s4v s5v s6v s7v (Z_to_bv 64 ar) (Z_to_bv 64 FB)
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 (al_sb AL)) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x98878) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s7v. intros D SZ1 SZ2 HC HND BUD BUDF PHI FFR UW Har. pose proof D as D0. gvA_open D. rt_facts. walk_prep.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as Dnn.
    (* [comment removed for export] *)
    pose proof CSG as CSG'. unfold SC in CSG'.
    lazymatch type of CSG' with rw_cells _ _ _ ?cs =>
      replace cs with ((pre ++ [CB 48 j48]) ++ [C8 (Z_to_bv 64 inext)] ++ ([C1 mg; CB 7 pad7] ++ post ++ [C8 (Z_to_bv 64 0)])) in CSG'
        by (repeat rewrite <- app_assoc; reflexivity) end.
    destruct (rw_cells_split3 asegs mc SIG _ _ _ CSG') as (_ & CNX & _). clear CSG'.
    rewrite !cells_size_app, SZ1 in CNX. cbn [cells_size csize Nat.add] in CNX. replace (SIG + Z.of_nat 80) with (SIG + 80) in CNX by (clear; lia).
    pose proof (chain_addr_range asegs _ _ _ _ _ _ _ HC) as IB.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    clear CNX.
    (* [comment removed for export] *)
    zstep. if_cases KZ; zify_cond KZ.
    - (* [comment removed for export] *)
      destruct nodes as [|n1 rest].
      2:{ exfalso. pose proof (chain_uncons asegs _ _ _ _ _ _ _ _ HC) as (-> & HIN2 & _ & HP2 & _).
          pose proof (blocks_below_hm R HIA hc _ _ mc _ HHc ltac:(intros b Hb; exact Hb)) as BB1. destruct (BB1 _ HIN2) as [_ C2]. cbn [fst snd] in C2. unfold NAME_SIZE in C2.
          first [change 18446744073709551615 with (Z.ones 64) in KZ; rewrite Z.land_ones in KZ by (clear - HP2 C2 ACV; lia) | idtac].
          first [change (2 ^ 64) with 18446744073709551616 in KZ | change (2 ^ Z.of_N 64) with 18446744073709551616 in KZ | idtac].
          rewrite ?Z.mod_small in KZ by (clear - HP2 C2 ACV; lia). rewrite ?unsigned_lit in KZ by (clear - HP2 C2 ACV; lia).
          clear - KZ HP2; lia. }
      intros moq [HKq MFq].
      eapply (AF0 FB sp1 PHIa FFRa) with (hc := hc) (mc := mc) (moc := moq) (ar := ar);
        first [ exact SZ1 | exact SZ2 | exact Har
              | eapply gvA_mo; [exact D0| exact HKq| exact MFq]
              | cbn [length] in PHI; unfold AVOL_CALL in *; clear - PHI; lia
              | cbn [length] in FFR; unfold fr_charge in *; clear - FFR Dnn; lia
              | match goal with |- ?g => idtac "OUT-AF0a-LEFT:" g end ].
    - (* [comment removed for export] *)
      destruct nodes as [|n1 rest]; [exfalso; cbn in HC; subst inext; clear - KZ; cbv in KZ; first [lia | congruence]|].
      pose proof (chain_uncons asegs _ _ _ _ _ _ _ _ HC) as (E1 & _). subst inext.
      intros moq [HKq MFq].
      eapply (loopN (n1 :: rest) n1 FB sp1 PHIa FFRa) with (hc := hc) (mc := mc) (moc := moq);
        first [ congruence | exact HC | exact HND | exact UW | exact BUD | exact BUDF
              | eapply gvA_mo; [exact D0| exact HKq| exact MFq]
              | idtac ].
      intros mc' moc' hc' y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 s5' G'.
      eapply (AF0 FB sp1) with (hc := hc') (mc := mc') (moc := moc') (ar := ar);
        first [ exact G' | exact SZ1 | exact SZ2 | exact Har | exact PHI | exact FFR
              | match goal with |- ?g => idtac "OUT-AF0b-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG NS1 HMND FREE STKn CNTn_mono NAM0 LFB PP0 CWP PPLO BIN B2 ALS SG0 CWS SGLO DSB DA0 CRDA DALO D1 D3 SLOS SLOL SLO TOP SPA SPH TPV LOS SLOq"] Lemma OUTA : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p : Z) (pre : list cell) (j48 : list byte) (inext : Z) (mg : byte) (pad7 : list byte) (post : list cell) (nodes : list Z) mc moc hc (ar : Z)
      (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v s5v s6v s7v s8v : word),
    gvA FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p (SC pre j48 inext mg pad7 post) (SNAME (rev nodes)) mc moc hc ->
    cells_size pre = 32%nat -> cells_size post = 96%nat ->
    name_chain asegs (fun _ => True) mc (SNAME (rev nodes) ++ LB) inext nodes -> List.NoDup nodes ->
    havol asegs R HIA h + PHIa + Z.of_nat (length nodes) * AVOL_CALL <= AVOL_MAX ->
    hfr asegs R HIA h + FFRa + Z.of_nat (length nodes) * fr_charge (d + 1) <= FR_MAX ->
    PHIa + Z.of_nat (length nodes) * AVOL_CALL <= PHIsi NB -> FFRa + Z.of_nat (length nodes) * fr_charge (d + 1) <= FFRsi NB d ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    -0x8000 < ar <= 0 ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 FB) (Z_to_bv 64 SIG) s4v s5v s6v s7v s8v (Z_to_bv 64 FB)
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 (al_sb AL)) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x98874) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s8v. intros D SZ1 SZ2 HC HND BUD BUDF PHI FFR UW Har. pose proof D as D0. gvA_open D. rt_facts.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    zstep.
    intros moq [HKq MFq].
    eapply (OUT FB sp1 PHIa FFRa) with (hc := hc) (mc := mc) (moc := moq) (ar := ar);
      first [ exact SZ1 | exact SZ2 | exact HC | exact HND | exact BUD | exact BUDF | exact PHI | exact FFR | exact UW | exact Har
            | eapply gvA_mo; [exact D0| exact HKq| exact MFq]
            | match goal with |- ?g => idtac "OUTA-LEFT:" g end ].
  Qed.
  End Call.
End Walk.
