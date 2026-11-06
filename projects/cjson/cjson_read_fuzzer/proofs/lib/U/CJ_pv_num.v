(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Arr FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat FmtFp FloatScan FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree CJ_print_iface CJ_utraps CJ_ensure CJ_pstr_B CJ_pv_common CJ_pv_ctx CJ_pv_update CJ_pv_cases CJ_pv_numA CJ_pv_numB NumFacts_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_shgetc_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require NumFacts_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_fmt_fp_lib F_printf_iface Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_facts3 Printf_model.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require JunkAbs.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Local Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Local Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Local Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.

Ltac killK K := first [exfalso; apply K; reflexivity | exfalso; revert K; lia_cj_nf].

Section S.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
            (m : word -> option byte)
            (SPB : Z) (LR B : list cblock) (n : nat) (p PB dep : Z) (fw : word) (lo : Z).
  Hypothesis PL : pb_place (bv_unsigned sp) PB SPB.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - PV_STACK n.
  Hypothesis TP : tp = wz PTP.
  Hypothesis SPhi : bv_unsigned sp <= 2^64.
  Hypothesis N1 : (1 <= n)%nat.
  Hypothesis BLR : forall b, In b B -> In b LR.
  Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
  Hypothesis DEP0 : 0 <= dep.
  Hypothesis PNZ : p <> 0.
  Hypothesis CH0 : cj_chain CJ_PRINTABLE m n p B.
  (* [comment removed for export] *)
  Hypothesis SPRD : F_printf_iface.sprintf_d_stmt.
  Hypothesis SPRG : forall prec, F_printf_iface.sprintf_g_stmt prec.
  Hypothesis SSC : Scan_iface.rsscanf_lg_stmt.
  Hypothesis GRET : F_printf_iface.FMT_G_RET.
  Hypothesis GLEN25 : F_printf_iface.FMT_G_LEN25.
  Hypothesis GFACTS : NUM_FMT_G_FACTS.
  Hypothesis GTOT : NUM_FMT_G_TOTAL.
  Hypothesis DTOT : NUM_FMT_D_TOTAL.
  Hypothesis SJUNK : NUM_SSCANF_JUNK.
  Hypothesis DEPN : dep + Z.of_nat n <= 2^40.

  Notation POST := (pvalue_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR B n p PB dep fw lo m).
  Notation SPF := (bv_unsigned sp + -128).
  Notation PVFRAME mm loc := (rw_cells usegs mm (bv_unsigned sp + -128)
     [CB 40 loc; C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation ACTX := (actx HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 F m SPB LR PB fw lo).
  Notation NCTX' := (NCTX HI sp m SPB LR PB fw lo).
  Notation PTST' := (PTST sp). Notation PTXT' := (PTXT sp).
  Notation PFH' := (PFH ra sp s0 s1 s2 s3 s4 s5 s6 s7 F).
  Notation FH := [C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Ltac useA L := eapply (L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR B n p PB dep fw lo PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0).

  (* [comment removed for export] *)
  Lemma frame_pieces : forall mm t mid,
    rw_cells usegs mm SPF ([C8 t] ++ mid ++ FH) -> cells_size mid = 32%nat ->
    PTST' mm t /\ PTXT' mm (cells_bytes mid) /\ PFH' mm.
  Proof.
    clear. intros mm t mid FR SZ.
    apply rw_cells_merge in FR. rewrite SZ in FR. cbn [app] in FR.
    apply (proj1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.rw_cells_app _ _ _ [C8 t] _)) in FR. destruct FR as [H1 FR].
    apply (proj1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.rw_cells_app _ _ _ [CB 32 (cells_bytes mid)] _)) in FR. destruct FR as [H2 H3].
    cbn [cells_size csize Nat.add] in H2, H3.
    replace (bv_unsigned sp + -128 + Z.of_nat 8) with (bv_unsigned sp + -120) in H2 by lia.
    replace (bv_unsigned sp + -128 + Z.of_nat 8 + Z.of_nat 32) with (bv_unsigned sp + -88) in H3 by lia.
    split; [exact H1|]. split; [exact H2| exact H3].
  Qed.

  Lemma pv_num : forall mm mo loc Fc fcc errv LB buf len off bs
      x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    ACTX dep mm mo loc Fc fcc errv LB buf len off bs ->
    SCPS usegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 x10 (Z_to_bv 64 p) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x14690) fcc None mm (seg_rom usegs)) mo.
  Proof.
    intros until x31. intros CTX.
    destruct (cj_chain_cons_inv _ _ _ _ _ CH0 PNZ) as (d0 & nx & pv & ch & ty & p1 & vs & vi & p2 & vd & ky & Bv & Bk & Bcc & Bn & Ed & ND & TY & _ & SV & SK & CHC & CHN & EB).
    assert (PIN : In (p, 64) B) by (rewrite EB; left; reflexivity).
    pose proof (actx_node HI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PL CEIL LO BLR _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ND (node_cells_size _ _ _ _ _ _ _ _ _ _) PIN) as NDn.
    unfold node_cells in NDn.
    pose proof (lh_block_range HI _ _ _ _ _ _ (proj1 CTX) ltac:(eapply Permutation_in; [exact (proj1 (proj2 CTX))| right; apply BLR; exact PIN])) as (_ & _ & _ & P4 & _). try rewrite alloc_ceiling_eq in P4.
    destruct (actx_nctx HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 F m SPB LR PB fw lo _ _ _ _ _ _ _ _ _ _ _ _ CTX) as (NC & FR & FRM & FA).
    pose proof NC as (HL & HP & PBS0 & ARR & LEN & PN & ST & ERR & MI & CJ & PVA).
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PV_STACK, PV_BASE in LO'. pose proof PL as (PL1 & PL2 & PL3 & PL4).
    unfold PERRNO in ERR.
    pose proof (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as (R1 & R2 & R3 & R4 & R5). try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
    pose proof (munch_refl [(SPF, SPF + 40)] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
    pose proof CJ as (CJa & (ge1 & ge2 & CJb) & CJc). unfold PHOOKS, PGERROR, PLCONV, PDOTSTR, PMALLOC, PFREE, PREALLOC, wz in CJa, CJb, CJc.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. step. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
    step. step. step. step.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K; first [killK K | idtac]; try clear K.
    zstep. step. if_cases K; zify_cond K; first [killK K | idtac]; try clear K.
    step. step. if_cases K; zify_cond K; first [killK K | idtac]; try clear K.
    step. step. step. step. step. step. fix_lit_store.
    lazymatch goal with |- context [zxb ?b] => change (zxb b) with (Z_to_bv 64 46) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m9 end.
    assert (NC0 : NCTX' dep m9 mo errv LB buf len off bs).
    { eapply (nctx_call HI sp m SPB LR n PB fw lo PL CEIL LO); [exact NC| exact MU| exact WM| exact MI| exact ST| unfold PERRNO; exact ERR|].
      intros iv [<-|[]]. left. cbn. lia. }
    step. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      pose proof (dfin_of_test vd K0) as DFIN.
      step. step. step.
      lazymatch type of FR with rw_cells _ _ _ (?a :: ?b :: ?c :: ?d :: ?e :: ?f :: ?rest) =>
        change (a :: b :: c :: d :: e :: f :: rest) with ([a] ++ [b; c; d; e; f] ++ rest) in FR end.
      destruct (frame_pieces _ _ _ FR eq_refl) as (H1 & H2 & H3).
      step. if_cases K1.
      + (* [comment removed for export] *) apply evt_done. cbv beta.
        eapply (num_G15 HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR B n p PB dep fw lo PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0 SPRG SSC GRET GLEN25 GFACTS GTOT SJUNK);
          [exact NC0| exact H1| exact H2| exact H3| assumption| | | exact DFIN].
        * repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]). exact FA.
        * intros r Hr. apply freg_get_same. rewrite Hr. reflexivity.
      + (* [comment removed for export] *) apply evt_done. cbv beta.
        eapply (num_D HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR B n p PB dep fw lo PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0 SPRD DTOT);
          [exact NC0| exact H1| exact H2| exact H3| assumption|].
        repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]). exact FA.
    - (* [comment removed for export] *)
      step. step.
      lazymatch type of FR with rw_cells _ _ _ (?a :: ?b :: ?c :: ?d :: ?e :: ?f :: ?rest) =>
        change (a :: b :: c :: d :: e :: f :: rest) with ([a] ++ [b; c; d; e; f] ++ rest) in FR end.
      apply rw_cells_merge in FR. cbn [cells_size csize cells_bytes cbytes Nat.add app] in FR.
      step. fix_lit_store. step. fix_lit_store. step. step.
      lazymatch type of FR with rw_cells _ _ _ (?a :: ?b :: ?c :: ?d :: ?rest) =>
        change (a :: b :: c :: d :: rest) with ([a] ++ [b; c; d] ++ rest) in FR end.
      destruct (frame_pieces _ _ _ FR eq_refl) as (H1 & H2 & H3).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m8 end.
      assert (NC1 : NCTX' dep m8 mo errv LB buf len off bs).
      { eapply (nctx_call HI sp m SPB LR n PB fw lo PL CEIL LO); [exact NC| exact MU| exact WM| exact MI| exact ST| unfold PERRNO; exact ERR|].
        intros iv [<-|[]]. left. cbn. lia. }
      apply evt_done. cbv beta.
      useA num_E; [eapply (nctx_actx HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 F m SPB LR PB fw lo); [exact NC1| eapply pieces_join; [exact H1| exact H2| exact H3]| assumption| repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]); exact FA]
                  | destruct H2 as [[W _] _]; cbn in W; destruct W as [W _]; exact W | lia].
  Qed.
End S.

Theorem pv_num_case : forall HI,
  F_printf_iface.sprintf_d_stmt -> (forall prec, F_printf_iface.sprintf_g_stmt prec) -> Scan_iface.rsscanf_lg_stmt ->
  F_printf_iface.FMT_G_RET -> F_printf_iface.FMT_G_LEN25 ->
  NUM_FMT_G_FACTS -> NUM_FMT_G_TOTAL -> NUM_FMT_D_TOTAL -> NUM_SSCANF_JUNK ->
  forall n, pv_case_at PV_NUM_ENTRY HI n.
Proof.
  intros HI SPRD SPRG SSC GRET GLEN25 GFACTS GTOT DTOT SJUNK n. unfold pv_case_at, PV_NUM_ENTRY.
  intros until lo. intros PL CEIL LO TP SPhi N1 BLR SPAL DEPN DEP0 PNZ CH0 REC. intros.
  eapply pv_num; eassumption.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac killK K := first [exfalso; apply K; reflexivity | exfalso; revert K; lia_cj_nf].
