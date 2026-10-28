(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_pkcs7_signers.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag
     A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt A_pkcs7_signers_A A_pkcs7_signers_B A_pkcs7_signers_C A_pkcs7_signers_D A_pkcs7_signers_E A_pkcs7_signers_F A_pkcs7_signers_G A_pkcs7_signers_H A_pkcs7_signers_I.
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
  Variables (PHIsi : Z -> Z) (FFRsi : Z -> Z -> Z) (CNTsi : Z -> Z) (STKsi : Z).
  Hypothesis SIGNER : pkcs7_signer_stmtA asegs R HIA PHIsi FFRsi CNTsi STKsi A_PKCS7_SIGNER.
  Hypothesis PHIsi_mono : forall n n', 0 <= n <= n' -> 0 <= PHIsi n <= PHIsi n'.
  Hypothesis FFRsi_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRsi n d <= FFRsi n' d.
  Hypothesis CNTsi_mono : forall n n', 0 <= n <= n' -> 0 <= CNTsi n <= CNTsi n'.
  Hypothesis STKsi0 : 0 <= STKsi.
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
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

  #[using="Type"] Lemma len_sb_cons : forall x ns r, length (signer_blocks ((x, ns) :: r)) = (length ns + 1 + length (signer_blocks r))%nat.
  Proof. clear - HIA. intros. cbn [signer_blocks fst snd]. rewrite !length_app, length_map. cbn [length]. unfold blk in *. lia. Qed.
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
  #[using="Type"] Lemma splink_presx0 : forall mA mB L1 SPx X a l e,
    splink asegs mA L1 a l e -> heap_presx asegs L L1 SPx X mA mB ->
    (forall x, In (x, SIGNER_SIZE) L1 -> In x (map fst l) -> disjoint_from X x SIGNER_SIZE) ->
    (forall inext names x, In names (map snd l) -> name_chain asegs (fun _ => True) mA L1 inext names -> In x names -> disjoint_from X x NAME_SIZE) ->
    splink asegs mB L1 a l e.
  Proof.
    clear - HIA. intros mA mB L1 SPx X a l e HSL HP HD1 HD2. eapply splink_mem; [exact HSL| intros x _ Hx; exact Hx| |].
    - intros x cs Hx Hl HR Hsz. eapply heap_presx_rw_cells; [exact HP| exact HR| eapply client_range_block; [exact Hx| lia| lia] | rewrite Hsz; apply HD1; assumption].
    - intros inext names Hn HN. eapply chain_presx; [exact HN| intros x Hx; eapply chain_nodes_in; [exact HN| exact Hx] | exact HP| unfold NAME_SIZE; lia|].
      intros x Hx. eapply HD2; eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition OPENA (mc : mem) (Lc : list blk) (inext0 : Z) (names0 : list Z) (S1 : Z) (mid : list (Z * list Z))
      (prev pinext : Z) (pnames : list Z) (psj : signer_junk) : Prop :=
    name_chain asegs (fun _ => True) mc (Lc ++ LB) inext0 names0
    /\ splink asegs mc (Lc ++ LB) S1 mid prev
    /\ rw_cells asegs mc prev (signer_cells pinext 0 psj) /\ name_chain asegs (fun _ => True) mc (Lc ++ LB) pinext pnames
    /\ prev mod 16 = 0 /\ 0 < prev /\ In (prev, SIGNER_SIZE) Lc
    /\ (prev + SIGNER_SIZE <= BUF \/ BUF + n <= prev)
    /\ ~ In prev (map fst mid)
    /\ Lc = sbl (mid ++ [(prev, pnames)]) ++ SNAME (rev names0)
    /\ fresh_apart R LB LF prev 200.

  #[using="Type"] Lemma CLOSEA : forall mc Lc inext0 names0 S1 mid prev pinext pnames psj,
    OPENA mc Lc inext0 names0 S1 mid prev pinext pnames psj -> signer_chain asegs mc (Lc ++ LB) S1 (mid ++ [(prev, pnames)]).
  Proof.
    clear - HIA. (intros mc Lc inext0 names0 S1 mid prev pinext pnames psj dd_H; ddestruct dd_H as (HN0 & HSP & PC & PN & PAL & PPOS & PIN & PVB & PNM & ELc & _)).
    apply splink_to_chain. eapply splink_snoc; [exact HSP| apply in_or_app; left; exact PIN| exact PAL| exact PPOS| exact PC| exact PN].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma len_sbl : forall l, length (sbl l) = length (signer_blocks l).
  Proof.
    clear - HIA. intros l. apply Permutation_length. apply sbl_perm.
  Qed.


  (* [comment removed for export] *)
  #[using="Type"] Lemma sbl_in_fst : forall l x, In x (map fst l) -> In (x, SIGNER_SIZE) (sbl l).
  Proof.
    clear - HIA. induction l as [|[a ns] r IH]; cbn; intros x Hx; [exact Hx|].
    destruct Hx as [<-|Hx]; apply in_or_app; [right| left; apply IH; exact Hx].
    apply in_or_app; right; left; reflexivity.
  Qed.
  #[using="Type"] Lemma sbl_in_snd : forall l names x, In names (map snd l) -> In x names -> In (x, NAME_SIZE) (sbl l).
  Proof.
    clear - HIA. induction l as [|[a ns] r IH]; cbn; intros names x Hn Hx; [exact Hn|].
    destruct Hn as [<-|Hn]; apply in_or_app; [right| left; eapply IH; eassumption].
    apply in_or_app; left. unfold SNAME. apply (in_map (fun y => (y, NAME_SIZE))). apply (proj1 (in_rev _ _)). cbn in Hx. exact Hx.
  Qed.
  #[using="Type"] Lemma SNAME_in : forall names x, In x names -> In (x, NAME_SIZE) (SNAME (rev names)).
  Proof. clear - HIA. intros names x Hx. unfold SNAME. apply (in_map (fun y => (y, NAME_SIZE))). apply (proj1 (in_rev _ _)). exact Hx. Qed.

  #[using="Type"] Lemma lenLc : forall Lc sg names0, Lc = sbl sg ++ SNAME (rev names0) ->
    Z.of_nat (length names0) + Z.of_nat (length (signer_blocks sg)) = Z.of_nat (length Lc).
  Proof.
    clear - HIA. intros Lc sg names0 ->. rewrite length_app, len_sbl. unfold SNAME. rewrite length_map, length_rev. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma OPENA_presx : forall mA mB Lc (L1 : list blk) SPx X inext0 names0 S1 mid prev pinext pnames psj,
    OPENA mA Lc inext0 names0 S1 mid prev pinext pnames psj ->
    heap_presx asegs L L1 SPx X mA mB ->
    (forall b, In b (Lc ++ LB) -> In b L1) ->
    (forall x k, In (x, k) Lc -> 0 < k -> disjoint_from X x k) ->
    OPENA mB Lc inext0 names0 S1 mid prev pinext pnames psj.
  Proof.
    clear - HIA. (intros mA mB Lc L1 SPx X inext0 names0 S1 mid prev pinext pnames psj dd_H; ddestruct dd_H as (HN0 & HSP & PC & PN & PAL & PPOS & PIN & PVB & PNM & ELc & PFR); intros HPX SUB HDX).
    assert (HPX1 : heap_presx asegs L (Lc ++ LB) SPx X mA mB).
    { eapply heap_presx_weaken; [exact HPX| exact SUB| apply Z.le_refl| intros x Hx; exact Hx]. }
    assert (INn : forall x, In x names0 -> In (x, NAME_SIZE) Lc).
    { intros x Hx. rewrite ELc. apply in_or_app; right. apply SNAME_in. exact Hx. }
    assert (INf : forall x, In x (map fst (mid ++ [(prev, pnames)])) -> In (x, SIGNER_SIZE) Lc).
    { intros x Hx. rewrite ELc. apply in_or_app; left. apply sbl_in_fst. exact Hx. }
    assert (INs : forall names x, In names (map snd (mid ++ [(prev, pnames)])) -> In x names -> In (x, NAME_SIZE) Lc).
    { intros names x Hn Hx. rewrite ELc. apply in_or_app; left. eapply sbl_in_snd; eassumption. }
    split.
    { eapply (chain_presx asegs L _ _ _ mA mB _ _ SPx X); [exact HN0| intros x Hx; eapply (chain_nodes_in asegs); [exact HN0| exact Hx]| exact HPX1| unfold NAME_SIZE; clear; lia|].
      intros x Hx. apply HDX; [apply INn; exact Hx| unfold NAME_SIZE; clear; lia]. }
    split.
    { eapply splink_presx0; [exact HSP| exact HPX1| |].
      - intros x _ Hl. apply HDX; [apply INf; rewrite map_app; apply in_or_app; left; exact Hl| unfold SIGNER_SIZE; clear; lia].
      - intros inext names x Hn _ Hx. apply HDX; [eapply INs; [rewrite map_app; apply in_or_app; left; exact Hn| exact Hx]| unfold NAME_SIZE; clear; lia]. }
    split.
    { eapply heap_presx_rw_cells; [exact HPX1| exact PC| eapply client_range_block; [apply in_or_app; left; exact PIN| clear; lia| cbn [cells_size csize Nat.add length signer_cells]; unfold SIGNER_SIZE; clear; lia]|].
      cbn [cells_size csize Nat.add length signer_cells]. apply (HDX prev 200); [exact PIN| clear; lia]. }
    split.
    { eapply (chain_presx asegs L _ _ _ mA mB _ _ SPx X); [exact PN| intros x Hx; eapply (chain_nodes_in asegs); [exact PN| exact Hx]| exact HPX1| unfold NAME_SIZE; clear; lia|].
      intros x Hx. apply HDX; [eapply INs; [rewrite map_app; apply in_or_app; right; left; reflexivity| exact Hx]| unfold NAME_SIZE; clear; lia]. }
    split; [exact PAL|]. split; [exact PPOS|]. split; [exact PIN|]. split; [exact PVB|]. split; [exact PNM|]. split; [exact ELc| exact PFR].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma presW_munch_cs : forall (hq : HST asegs R HIA) (LBq LFq : list blk) SP SSP W m0 mA mB W',
    presW asegs R HIA h LBq LFq SP SSP W m0 mA -> munch W' mA mB -> wmono asegs mA mB ->
    (forall x, hcs asegs R HIA h x -> hcs asegs R HIA hq x) -> w_client (hcs asegs R HIA hq) W' ->
    Forall (fun iv => wcover R LBq LFq SP W (fst iv) (snd iv - fst iv)) W' ->
    presW asegs R HIA h LBq LFq SP SSP W m0 mB.
  Proof.
    (intros hq LBq LFq SP SSP W m0 mA mB W' dd_H; ddestruct dd_H as (PW & CW1 & CW2 & CW3); intros MU WM HCS HW HC).
    split; [| split; [exact CW1| split; [exact CW2| exact CW3]]].
    eapply presA_trans; [exact PW|]. split.
    - intros a Ha Hc Ho. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha.
      destruct (outside_dec W' a) as [Y|N]; [exact Y|]. exfalso.
      ddestruct (not_outside_in W' a N) as (lo' & hi' & HIn & Hr).
      rewrite Forall_forall in HC. exact (HC (lo', hi') HIn a ltac:(cbn; clear - Hr; lia) Hc Ho).
    - intros c Hc Hr. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Hr.
      pose proof (hcs_ok asegs R HIA hq) as OK. destruct OK as (K1 & _). apply (outside_of_not_cs (hcs asegs R HIA hq)); [exact HW|].
      exact (proj2 (proj2 (proj2 (K1 c (HCS c (CW1 c Hc)))))).
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma aobj_back : forall (CS1 CS2 : Z -> Prop) mq A k, aobj asegs AL CS2 mq A k -> crange CS1 A k -> aobj asegs AL CS1 mq A k.
  Proof. intros CS1 CS2 mq A k [_ HS] HC. split; [exact HC| exact HS]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND FREE STKsi CNTsi_mono LFB PP0 CWP PPLO BIN B1 B2 B3 DPB ALS SG0 CWS SGLO DSB DA0 CRDA DALO D1 D2 D3 SLOS SLOL SLO TOP SPA SPH TPV LOS"] Lemma LOOP_cfail : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k16 : word) (j32 : list byte)
      (p inext0 : Z) (names0 : list Z) (sjh : signer_junk) (S1 : Z) (sg : list (Z * list Z))
      (Lc : list blk) mc moc hc
      (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v s5v s6v s7v s8v s11v : word),
    gvA FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 (Z_to_bv 64 (-22400)) (Z_to_bv 64 SIG) k16 (Z_to_bv 64 DALG) j32 p (signer_cells inext0 S1 sjh) Lc mc moc hc ->
    name_chain asegs (fun _ => True) mc (Lc ++ LB) inext0 names0 -> signer_chain asegs mc (Lc ++ LB) S1 sg -> Lc = sbl sg ++ SNAME (rev names0) ->
    havol asegs R HIA h + PHIa + Z.of_nat (length Lc) * AVOL_CALL <= AVOL_MAX ->
    hfr asegs R HIA h + FFRa + Z.of_nat (length Lc) * fr_charge (d + 1) <= FR_MAX ->
    PHIa + Z.of_nat (length Lc) * AVOL_CALL <= PHIs PHIsi CNTsi NB ->
    FFRa + Z.of_nat (length Lc) * fr_charge (d + 1) <= FFRs FFRsi CNTsi NB d ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 FB) s7v s4v s5v s6v (Z_to_bv 64 (al_sb AL)) s8v (Z_to_bv 64 FB)
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) s11v t3 t4 t5 t6)
                 F (Z_to_bv 64 0x98c14) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s11v. intros D HN0 HSC ELc BUD BUDF PHI FFR UW. pose proof D as D0. gvA_open D. rt_facts. walk_prep.
    pose proof (lenLc _ _ _ ELc) as EL.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. try (if_cases KZ; zify_cond KZ; [| exfalso; clear - KZ; cbv in KZ; first [lia | congruence]]).
    zstep. zstep.
    intros moq [HKq MFq].
    eapply (CLEAN R HIA) with (STKsi := STKsi) (names0 := names0) (sg := sg) (inext0 := inext0) (snext := S1) (sjh := sjh)
                              (PHIa := PHIa) (FFRa := FFRa) (slo := slo) (d := d) (lo := lo) (hc := hc) (mc := mc) (moc := moq) (r := -22400);
      first [ exact UW | sec_hyps
            | lazymatch goal with
              | |- name_chain _ _ _ _ _ _ => rewrite <- ELc; exact HN0
              | |- signer_chain _ _ _ _ _ => rewrite <- ELc; exact HSC
              | |- _ < -22400 < _ => clear; lia
              | |- havol _ _ _ _ + _ + _ <= _ => rewrite EL; exact BUD
              | |- hfr _ _ _ _ + _ + _ <= _ => rewrite EL; exact BUDF
              | |- _ + _ * AVOL_CALL <= _ => rewrite EL; exact PHI
              | |- _ + _ * fr_charge _ <= _ => rewrite EL; exact FFR
              end
            | (lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signers_C.gvA] => idtac end end;
               rewrite <- ELc; first [ eapply gvA_mo; [exact D0| exact HKq| exact MFq] | match goal with |- ?g => idtac "CFAIL-GVA-LEFT:" g end ])
            | match goal with |- ?g => idtac "CFAIL-LEFT:" g end ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND FREE STKsi CNTsi_mono LFB PP0 CWP PPLO BIN B1 B2 B3 DPB ALS SG0 CWS SGLO DSB DA0 CRDA DALO D1 D2 D3 SLOS SLOL SLO TOP SPA SPH TPV LOS"] Lemma LOOP_sfail : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k16 : word) (j32 : list byte)
      (p inext0 : Z) (names0 : list Z) (sjh : signer_junk) (S1 : Z) (sg : list (Z * list Z))
      (Lc : list blk) (Sn r : Z) mc moc hc
      (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v s5v s6v s7v s11v : word),
    gvA FB sp1 X0 PHIa FFRa w0 w1 w2 lw b4 (Z_to_bv 64 (-22400)) (Z_to_bv 64 SIG) k16 (Z_to_bv 64 DALG) j32 p (signer_cells inext0 S1 sjh) ((Sn, 200) :: Lc) mc moc hc ->
    name_chain asegs (fun _ => True) mc (Lc ++ LB) inext0 names0 -> signer_chain asegs mc (Lc ++ LB) S1 sg -> Lc = sbl sg ++ SNAME (rev names0) ->
    -0x10000 < r <= 0 -> r <> 0 ->
    havol asegs R HIA h + PHIa + (1 + Z.of_nat (length Lc)) * AVOL_CALL <= AVOL_MAX ->
    hfr asegs R HIA h + FFRa + (1 + Z.of_nat (length Lc)) * fr_charge (d + 1) <= FR_MAX ->
    PHIa + (1 + Z.of_nat (length Lc)) * AVOL_CALL <= PHIs PHIsi CNTsi NB ->
    FFRa + (1 + Z.of_nat (length Lc)) * fr_charge (d + 1) <= FFRs FFRsi CNTsi NB d ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 FB) s7v s4v s5v s6v (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 Sn) (Z_to_bv 64 FB)
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) s11v t3 t4 t5 t6)
                 F (Z_to_bv 64 0x98cf8) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s11v. intros D HN0 HSC ELc Hr RNZ BUD BUDF PHI FFR UW. pose proof D as D0. gvA_open D. rt_facts. walk_prep.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as Dnn.
    pose proof (lenLc _ _ _ ELc) as EL.
    pose proof (blocks_below_hm R HIA hc _ _ mc _ HHc ltac:(intros b Hb; exact Hb)) as BBc.
    destruct (BBc (Sn, 200) ltac:(apply in_or_app; left; left; reflexivity)) as [NP NCE]. cbn [fst snd] in NP, NCE.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (Z_to_bv 64 431228) with (Z_to_bv 64 (arl_free R)) by (rewrite FREE; reflexivity).
    assert (TST1 : forall q, bv_unsigned sp <= q < hstkhi asegs R HIA h -> outside X0 q).
    { intros q Hq. cbn [outside]. split; [clear - Hq PPLO LOS SLO NS1 STKsi0 NRT; lia| split; [clear - Hq SGLO LOS SLO NS1 STKsi0 NRT; lia| exact I]]. }
    eapply (free_stepA R HIA) with (STKsi := STKsi) (hc := hc) (moc := moc) (mc := mc) (Lc := (Sn, 200) :: Lc) (x := Sn) (k := 200)
                                   (PHIa := PHIa) (FFRa := FFRa) (slo := slo) (d := d) (W := X0) (lo := lo);
      first [ exact D0 | exact UW | exact TST1 | sec_hyps
            | lazymatch goal with
              | |- In (Sn, 200) _ => left; reflexivity
              | |- List.NoDup _ => exact (HMND _ _ _ _ HHc)
              | |- havol _ _ _ _ + _ + _ <= _ => unfold AVOL_CALL in *; clear - BUD; lia
              | |- hfr _ _ _ _ + _ + _ <= _ => unfold fr_charge in *; clear - BUDF Dnn; nia
              | |- 0 <= _ < 2 ^ 64 => clear; lia
              | |- _ mod 2 = 0 => reflexivity
              | |- forall m1 mo1 h1, _ => idtac
              end
            | match goal with |- ?g => idtac "SFAIL-FREE-LEFT:" g end ].
    cbv beta. intros m1 mo1 h1 z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 G1 HPf.
    (* [comment removed for export] *)
    lazymatch type of G1 with context [lb_remove ?x ?l] => replace (lb_remove x l) with Lc in G1 by (cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity) end.
    lazymatch type of HPf with context [lb_remove ?x ?l] => replace (lb_remove x l) with (Lc ++ LB) in HPf by (cbn [lb_remove fst app]; rewrite Z.eqb_refl; reflexivity) end.
    assert (HPX1 : heap_presx asegs L (Lc ++ LB) sp1 [] mc m1).
    { eapply heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HPf)| intros b Hb; apply in_or_app; left; exact Hb| apply Z.le_refl| intros x Hx; exact Hx]. }
    assert (HN1 : name_chain asegs (fun _ => True) m1 (Lc ++ LB) inext0 names0).
    { eapply (chain_presx asegs L _ _ _ mc m1 _ _ sp1 []); [exact HN0| intros x Hx; eapply (chain_nodes_in asegs); [exact HN0| exact Hx]| exact HPX1| unfold NAME_SIZE; clear; lia| intros; exact I]. }
    assert (HSC1 : signer_chain asegs m1 (Lc ++ LB) S1 sg).
    { eapply (signer_chain_presx0 R mc m1 _ _ sp1 []); [exact HSC| intros b Hb; eapply (signer_blocks_in asegs); [exact HSC| exact Hb]| exact HPX1| intros; exact I]. }
    clear HHc PRES STlo MIc SSc HPf.
    intros moq [HKq MFq].
    eapply (CLEAN R HIA) with (STKsi := STKsi) (names0 := names0) (sg := sg) (inext0 := inext0) (snext := S1) (sjh := sjh)
                              (PHIa := PHIa + AVOL_CALL) (FFRa := FFRa + fr_charge (d + 1)) (slo := slo) (d := d) (lo := lo) (hc := h1) (mc := m1) (moc := moq) (r := r);
      first [ exact UW | sec_hyps
            | lazymatch goal with
              | |- name_chain _ _ _ _ _ _ => rewrite <- ELc; exact HN1
              | |- signer_chain _ _ _ _ _ => rewrite <- ELc; exact HSC1
              | |- _ < r < _ => clear - Hr; lia
              | |- havol _ _ _ _ + _ + _ <= _ => rewrite EL; unfold AVOL_CALL in *; clear - BUD; lia
              | |- hfr _ _ _ _ + _ + _ <= _ => rewrite EL; unfold fr_charge in *; clear - BUDF; lia
              | |- _ + _ * AVOL_CALL <= _ => rewrite EL; unfold AVOL_CALL in *; clear - PHI; lia
              | |- _ + _ * fr_charge _ <= _ => rewrite EL; unfold fr_charge in *; clear - FFR; lia
              end
            | (lazymatch goal with |- ?g => lazymatch g with context [A_pkcs7_signers_C.gvA] => idtac end end;
               rewrite <- ELc; first [ eapply gvA_mo; [exact G1| exact HKq| exact MFq] | match goal with |- ?g => idtac "SFAIL-GVA-LEFT:" g end ])
            | match goal with |- ?g => idtac "SFAIL-LEFT:" g end ].
  Qed.
  End Call.
End Walk.
