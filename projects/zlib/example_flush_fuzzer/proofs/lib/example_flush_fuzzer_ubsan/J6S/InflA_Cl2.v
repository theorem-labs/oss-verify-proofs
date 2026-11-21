(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateGarbBase.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvTab.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ItCovIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvCov.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvTbl.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.Riscv Require Import Instr.
From LinuxProcessSemantics.Riscv Require Import Decode.
From LinuxProcessSemantics.Riscv Require Import DecodeC.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import CatExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import CatSim.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import SeqExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Tac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import MemRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateState.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Inflate.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Callee6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import IS6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflRod6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflCtx6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflArmLib6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflArmLib6b.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflNeed6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflA_Match2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflDec6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflA_Len3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflA_Len7.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import Callee6i.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflMem2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require InflA_ClS.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require InflA_Cl1.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflA_Dist3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InffastSafe IfSpec IfSpec6 InflA_LenF.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvArms5.

Module InflA_Codelens6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InftreesCoverage.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ItCovIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvCov.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvTbl.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inftrees.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S.Segs6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S.Callee6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflA_Match2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflDec6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflA_Len3.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflA_Len7.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.Callee6i.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem2.
Import InflA_ClS.InflA_CodelensS.
Import InflA_Cl1.InflA_Codelens5.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent bkv sbv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition cd_facts (v : icv) (s : inflate_state) (c : icall) : Prop :=
  is_sane s = 1
  /\ 0 <= is_whave s <= is_wsize s /\ 0 <= is_wnext s <= is_wsize s
  /\ arr_len (is_window s) = cv_WN v /\ (is_wsize s = 0 \/ is_wsize s = cv_WN v)
  /\ (forall i, 0 <= i < cv_WN v -> 0 <= arr_get (is_window s) i < 256)
  /\ CINV (cv_NI v) (cv_NO v) c
  /\ 257 <= is_nlen s <= 286 /\ 1 <= is_ndist s <= 30
  /\ (forall i, 0 <= i < is_nlen s + is_ndist s -> 0 <= arr_get (is_lens s) i <= 15)
  /\ arr_len (is_lens s) = 320 /\ arr_len (is_work s) = 288 /\ arr_len (is_codes s) = 1444
  /\ (forall i, 0 <= i < 320 -> 0 <= arr_get (is_lens s) i < 65536)
  /\ (forall i, 0 <= i < 288 -> 0 <= arr_get (is_work s) i < 65536)
  /\ (forall i, 0 <= i < 1444 -> 0 <= arr_get (is_codes s) i < 2 ^ 32).

Lemma cd_facts_S1 : forall v s c r1,
  cd_facts v s c -> arr_len (it_tbl r1) = 1444 -> arr_len (it_work r1) = 288 ->
  (forall i, 0 <= i < 288 -> 0 <= arr_get (it_work r1) i < 65536) -> (forall i, 0 <= i < 1444 -> 0 <= arr_get (it_tbl r1) i < 2 ^ 32) ->
  cd_facts v (cd_S1 s r1) c.
Proof.
  intros v s c r1 HD L1 L2 W1 T1. unfold cd_facts, cd_S1 in *. destruct s; cbn in *.
  destruct HD as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
  repeat (split; [assumption|]). exact T1.
Qed.

Lemma len_facts_cdS2 : forall v s c r2,
  cd_facts v s c -> is_lencode s = CDyn 0 -> 0 <= is_next s <= 852 ->
  tab_ok LENS (cat (it_tbl r2) (CDyn 0)) (is_lenbits s) (is_next s) = true ->
  tab_ok DISTS (cat (it_tbl r2) (CDyn (is_next s))) (it_bits r2) (it_table r2 - is_next s) = true ->
  is_next s + 2 <= it_table r2 <= is_next s + 592 ->
  len_facts v (cd_S2 s r2) c.
Proof.
  intros v s c r2 HD ELC NX1 TL2 TD2 NX2.
  destruct HD as (Hsane & Hwh & Hwn & Hwl & Hws & Hwb & CI & QN & QD & QL15 & Alens & Awork & Acodes & Blens & Bwork & Bcodes).
  unfold len_facts, cd_S2. destruct s; cbn in *. subst is_lencode. cbn.
  refine (conj Hsane (conj Hwh (conj Hwn (conj Hwl (conj Hws (conj Hwb (conj CI (conj _ (conj _ (conj _ _)))))))))).
  - exists is_next. split; [exact TL2 | lia].
  - cbn. lia.
  - exists (it_table r2 - is_next). split; [exact TD2 | lia].
  - cbn. lia.
Qed.

Lemma MFRAME_itable : forall v p M M' pbo,
  ictx v -> 0 <= p -> (pbo = 136 \/ pbo = 140) -> (forall x, M x <> None -> M' x <> None) -> agree_out (ITF v pbo) M M' -> MFRAME v p p M M'.
Proof.
  intros v p M M' pbo C Hp Hpb Hg Hag. split; [lia|]. split; [exact Hg|].
  intros x N1 N2 N3 N4. apply Hag. unfold ITF, in_franges, INF_FRAME, INF_SCRATCH in *. clear - N1 N2 Hpb. lia.
Qed.

Definition ilCB : cfg := CFG [] [] arm_rets (pc6_disp :: arm_stops) [].

Section SegB.
  Variable v : icv.
  Hypothesis C : ictx v.
  Hypothesis ITABLE : itable_run6.
  Hypothesis IFAST : inflate_fast_spec6.
  Hypothesis FFOK : ffok_stmt.
  Hypothesis FASTOK : fastok_stmt.
  Hypothesis GFOB : gfast_ob_stmt.
  Hypothesis FFRAME : fframe_stmt.

  Definition BREG (s : inflate_state) (c : icall) (r : iregs) (ret : Z) (R : bvmap 5 word) : Prop :=
    getr R 2 = zw (cv_sp v - INF_FRAME) /\ getr R 8 = zw (cv_S v) /\ getr R 20 = zw 16209
    /\ getr R 22 = zw (cv_S v + 168) /\ getr R 25 = zw A6_JTAB
    /\ getr R 3 = getr (cv_R0 v) 3 /\ getr R 4 = getr (cv_R0 v) 4
    /\ LVARK v (mkW s c r) R /\ getr R 10 = zw ret.

  Definition bpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (20, ELit 16209); (22, EAdd (EVar 33%nat) (ELit 168)); (25, ELit 0x12510);
     (18, EVar 36%nat); (19, EAdd (EVar 37%nat) (EVar 38%nat)); (9, EVar 39%nat); (23, EVar 40%nat); (24, EVar 41%nat);
     (27, EAdd (EVar 43%nat) (EVar 44%nat)); (10, EVar 45%nat)].

  Ltac open_cd HD :=
    destruct HD as (Hsane & Hwh & Hwn & Hwl & Hws & Hwb & CI & QN & QD & QL15 & Alens & Awork & Acodes & Blens & Bwork & Bcodes).

  Lemma codelens_segB : forall s c r R M ret,
    is_mode s = CODELENS -> cd_facts v s c -> RINV (cv_NI v) (cv_NO v) r -> ir_ret r = 0 -> (ret = 0 \/ ret = 1 \/ ret = -1) ->
    (ret = 0 -> is_lencode s = CDyn 0 /\ 0 <= is_next s <= 852 /\ 1 <= is_lenbits s <= 15
               /\ tab_ok LENS (cat (is_codes s) (CDyn 0)) (is_lenbits s) (is_next s) = true) ->
    (ret = 0 -> it_ret (cd_call2 s) = 0 -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW (iset_mode (cd_S2 s (cd_call2 s)) LEN_) c (irset_ret r 0))) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> BREG s c r ret R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d99c) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (cdB_res (cv_flush v) s c r ret) R' M' pc'.
  Proof.
    intros s c r R M ret Hmode HD RI Hret0 Hret HT HPL HM HRC HX HR. pose proof HD as HD0. open_cd HD.
    destruct HR as (G2 & G25 & G19 & G21 & G24 & G3 & G4 & HV & G10). unfold INF_FRAME in G2. unfold A6_JTAB in G24.
    pose proof HV as X; unfold LVARK in X; cbn [w_r] in X; destruct X as (G9 & G18 & G8 & G22 & G23 & G26).
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI. open_frame Mfr. rewrite ?Z.add_0_r in Fd0. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (Hrm : 0 <= ret mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    rewrite <- (zw_mod ret) in G10.
    unfold cdB_res.
    destruct (Z.eq_dec ret 0) as [R0|R0].
    -
      subst ret. cbn [Z.eqb negb]. change (0 mod 2 ^ 64) with 0 in G10. destruct (HT eq_refl) as (ELC & NX1 & LB1 & TL1). clear HT.
      replace (irset_ret r 0) with r by (rewrite <- Hret0; destruct r; reflexivity).
      pose proof (is6_next _ _ _ _ Msc) as C144. pose proof (is6_nlen _ _ _ _ Msc) as C132. pose proof (is6_ndist _ _ _ _ Msc) as C136.
      arm_symexP (@nil (Z * expr)) ilCB 20%nat [true]
        [RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (EVar 48%nat); RVal (EAdd (EVar 33%nat) (ELit 160));
         RVal (EAdd (EVar 33%nat) (ELit 140)); RVal (EAdd (EVar 33%nat) (ELit 808))]
        bpins [(45%nat, 1); (46%nat, 2 ^ 63); (47%nat, 512); (48%nat, 64)] v r
        [0; cv_S v + 1384 + 4 * is_next s; is_nlen s; is_ndist s] NoVals F0
        (mkst R (Z_to_bv 64 0x1d99c) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTB1" G end.
      set (M1 := wbytes M (zw (cv_S v + 128)) (Z_to_le_bytes 8 (cv_S v + 1384 + 4 * is_next s))) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 140)) (Z_to_le_bytes 4 6)) in *.
      set (sA := iset_distcode s (CDyn (is_next s))). set (sB := iset_distbits sA 6).
      assert (HM1 : LMEM v (mkW sA c r) M1).
      { apply (LMEM_store_scalar v C s c r _ M 128 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        exact (is6_upd_distcode M (cv_S v) _ s (CDyn (is_next s)) Msc ltac:(clear - CS; lia) ltac:(clear - CS; unfold is6_SIZE; lia)). }
      assert (HM2 : LMEM v (mkW sB c r) M2).
      { apply (LMEM_store_scalar v C sA c r _ M1 140 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_distbits M1 (cv_S v) _ sA 6 (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      pose proof HM2 as HM2'. clear Mrod Msc Mlens Mwork Mcodes Mwin Minp Mout Mzs Mfr Moutc Mmap_f Mmap_Z Mmap_S Mmap_P Mmap_W.
      clear Fsv F104 F96 F88 F72 F56 F48 F40 F32 F24 F16 F8 Fd0 C144 C132 C136.
      open_lmem HM2'. unfold mapped in *.
      pose proof (is6_next _ _ _ _ Msc) as C144. pose proof (is6_distbits _ _ _ _ Msc) as C124. cbn [w_s] in C144, C124.
      replace (is_next sB) with (is_next s) in C144 by (subst sB sA; destruct s; reflexivity).
      replace (is_distbits sB) with 6 in C124 by (subst sB sA; destruct s; reflexivity).
      replace (is_lens sB) with (is_lens s) in Mlens by (subst sB sA; destruct s; reflexivity).
      replace (is_work sB) with (is_work s) in Mwork by (subst sB sA; destruct s; reflexivity).
      replace (is_codes sB) with (is_codes s) in Mcodes by (subst sB sA; destruct s; reflexivity).
      symex_reg HR1 (10%bv : reg) as Q10. symex_reg HR1 (11%bv : reg) as Q11. symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (13%bv : reg) as Q13.
      symex_reg HR1 (14%bv : reg) as Q14. symex_reg HR1 (15%bv : reg) as Q15. symex_reg HR1 (1%bv : reg) as Q1. symex_reg HR1 (26%bv : reg) as Q27.
      destruct (ITABLE M2 R1 DISTS (cv_S v) (is_nlen s) (is_ndist s) (is_next s) 6 (cv_S v + 140) (cv_sp v - 224) (zw 0x1dbe0) (is_lens s) (is_codes s) (is_work s)
                  Q10 ltac:(rewrite Q11; f_equal; lia) Q12 Q13 Q14 Q15 ltac:(rewrite (Hfr1 (2%bv : reg) eq_refl); exact G2) Q1
                  ltac:(apply ret_ok_lit; [lia | reflexivity]) ltac:(right; reflexivity)
                  ltac:(clear - CS; lia) ltac:(clear - CS; lia) ltac:(clear - CS; lia) CoS
                  ltac:(unfold ITFR6, IMG6_TOP in *; clear - Csp; lia) ltac:(clear - Csp; lia) ltac:(clear - Csp47; lia)
                  ltac:(clear - Csp; replace (cv_sp v - 224) with (cv_sp v + (-14) * 16) by lia; rewrite Z.mod_add by lia; destruct Csp as (_ & _ & E); exact E)
                  ltac:(unfold ITFR6; clear - CSb; lia))
        as (R3 & M3 & HmsT & T10 & Tret & T2 & Tfr & Tlens & Tcodes & Twork & Tnext & Tbits & TLt & TLw & TRt & TRw & Tsh & Tg & Tag).
      { intros x Hx. apply Mmap_f. unfold ITFR6 in Hx. clear - Hx. lia. }
      { exact Mmap_S. }
      { exact Mrod. }
      { exact Alens. } { exact Acodes. } { exact Awork. }
      { exact Mlens. } { exact Mcodes. } { exact Mwork. }
      { exact C144. } { exact C124. }
      { exact Blens. } { exact Bcodes. } { exact Bwork. }
      { clear - QN; lia. } { clear - QN QD; lia. } { clear - QD; lia. }
      { intros i Hi. apply (proj2 (QL15 (is_nlen s + i) ltac:(clear - Hi QN; lia))). }
      { intros X; discriminate X. }
      { intros _; clear - QD; lia. }
      { lia. } { clear - NX1; lia. } { cbn [it_room]; unfold ENOUGH_DISTS; clear - NX1; lia. }
      change (inflate_table DISTS (is_lens s) (is_nlen s) (is_ndist s) (is_codes s) (is_next s) 6 (is_work s)) with (cd_call2 s) in *.
      set (r2 := cd_call2 s) in *.
      (* 1.4: the distance table's bits pointer is S + 140 (lenbits at 136); 1.3.1 had 124 / 120 *)
      assert (ES2 : iset_work (iset_codes (iset_next (if 140 =? 136 then iset_lenbits sB (it_bits r2) else iset_distbits sB (it_bits r2)) (it_table r2)) (it_tbl r2)) (it_work r2) = cd_S2 s r2)
        by (cbn [Z.eqb]; subst sB sA; unfold cd_S2; destruct s; reflexivity).
      pose proof (LMEM_itable v C sB c r M2 M3 140 (it_table r2) (it_bits r2) (it_tbl r2) (it_work r2) HM2 Hput ltac:(right; reflexivity)
                    (ITF_agree v 140 M2 M3 Tag) Tg Tcodes Twork Tnext Tbits) as HM3. rewrite ES2 in HM3.
      assert (HX3 : LX v (mkW (cd_S2 s r2) c r)).
      { apply (LX_step0 v s c r _ c r HX NH NB); unfold cd_S2; try (destruct s; reflexivity); [destruct s; cbn; cbn in Xlive; exact Xlive | exact Xret | exact Xmsg]. }
      assert (HC3 : CREG v (cd_S2 s r2) c r (it_ret r2) R3).
      { unfold CREG, INF_FRAME, LVARK, A6_JTAB. cbn [w_r]. split; [exact T2|].
        repeat match goal with |- _ /\ _ => split end;
          first [ exact T10
                | rewrite (Tfr (26%bv : reg) eq_refl); exact Q27
                | lazymatch goal with |- getr _ ?n = _ => rewrite (Tfr n eq_refl), (Hfr1 n eq_refl); assumption end
                | match goal with |- ?G => idtac "CREG LEFT" G end ]. }
      assert (HLF : it_ret r2 = 0 -> len_facts v (cd_S2 s r2) c).
      { intros R2.
        pose proof (tab_ok_of_shape DISTS (is_lens s) (is_nlen s) (is_ndist s) (is_codes s) (is_next s) 6 (is_work s) ltac:(clear - QD; lia)
                      ltac:(intros i Hi; apply QL15; clear - Hi QN; lia)
                      ltac:(intros X; discriminate X) ltac:(intros _; clear - QD; lia) ltac:(lia) ltac:(clear - NX1; lia)
                      ltac:(cbn [it_room]; unfold ENOUGH_DISTS; rewrite Acodes; clear - NX1; lia) ltac:(rewrite Awork; clear - QD; lia)) as TS2.
        change (inflate_table DISTS (is_lens s) (is_nlen s) (is_ndist s) (is_codes s) (is_next s) 6 (is_work s)) with r2 in TS2.
        cbv zeta in TS2. destruct (TS2 R2) as (TD2 & BD2 & NX2 & _ & OUT2). cbn [it_room] in NX2. unfold ENOUGH_DISTS in NX2.
        assert (TL2 : tab_ok LENS (cat (it_tbl r2) (CDyn 0)) (is_lenbits s) (is_next s) = true).
        { apply (tab_ok_ext LENS (cat (is_codes s) (CDyn 0))). 2:{ exact TL1. }
          intros i Hi. cbn [cat]. apply OUT2. clear - Hi; lia. }
        exact (len_facts_cdS2 v s c r2 HD0 ELC NX1 TL2 TD2 ltac:(clear - NX2 BD2; unfold it_bits, it_table in *; match type of BD2 with 1 <= ?b <= 15 /\ _ => assert (2 <= 2 ^ b) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia) | 1 <= ?b <= 15 => assert (2 <= 2 ^ b) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia) end; lia)). }
      destruct (codelens_segC v C IFAST FFOK FASTOK GFOB FFRAME (cd_S2 s r2) c r R3 M3 (it_ret r2) ltac:(unfold cd_S2; destruct s; exact Hmode) HLF RI0 Tret (HPL eq_refl) HM3 HX3 HC3)
        as (R' & M' & pc' & Hms3 & HPOST).
      exists R', M', pc'. split.
      { apply (msteps_trans _ _ (mkst R1 (Z_to_bv 64 0x1f188) M2 s6_rom)); [subst M2 M1; by_run Hms1 | eapply msteps_trans; [exact HmsT | exact Hms3]]. }
      apply (arm_post_chain v (mkW s c r) (mkW (cd_S2 s r2) c r) M M3); [unfold cd_S2; destruct s; split; [reflexivity | split; reflexivity] | | exact HPOST].
      cbn [w_r]. apply (MFRAME_trans v (ir_put r) (ir_put r) (ir_put r) M M2 M3); [| exact (MFRAME_itable v (ir_put r) M2 M3 140 C (proj1 Hput) ltac:(right; reflexivity) Tg (ITF_agree v 140 M2 M3 Tag))].
      subst M2 M1. do 2 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
      apply MFRAME_refl.
    -
      replace (negb (ret =? 0)) with true by (symmetry; rewrite Bool.negb_true_iff; apply Z.eqb_neq; exact R0).
      assert (Hrm0 : ret mod 2 ^ 64 <> 0).
      { intros E. apply R0. destruct Hret as [H|[H|H]]; subst ret; [reflexivity | discriminate E | discriminate E]. }
      assert (HretB : - 2 ^ 31 <= ret < 2 ^ 31) by (clear - Hret; lia). clear Hret.
      assert (Hrm1 : 0 < ret mod 2 ^ 64) by (clear - Hrm0 Hrm; lia). clear Hrm0 R0.
      arm_symexP (@nil (Z * expr)) ilCB 20%nat [false]
        [RVal (EVar 34%nat); RVal (EVar 35%nat); RVal (ELit 18446744073709535436)]
        bpins [(45%nat, 2 ^ 64)] v r [ret mod 2 ^ 64] NoVals F0
        (mkst R (Z_to_bv 64 0x1d99c) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTB2" G end.
      rewrite le8_mod64 in Hms1.
      set (r' := irset_ret r ret) in *. set (c' := icset_msg c MSG_invalid_literal_lengths_set) in *. set (s' := iset_mode s BAD) in *.
      set (M1 := wbytes M (zw (cv_sp v - 224 + 64)) (Z_to_le_bytes 8 ret)) in *.
      set (M2 := wbytes M1 (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66434)) in *.
      set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      assert (Hput' : 0 <= ir_put r' <= cv_NO v) by (subst r'; exact Hput).
      assert (HM1 : LMEM v (mkW s c r') M1) by (apply (LMEM_store_fscratch v C s c r' M 64 _ (LMEM_regs v s c r c r' M HM eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) Hput'); split; [left; reflexivity | reflexivity]).
      assert (HM2 : LMEM v (mkW s c' r') M2) by (exact (LMEM_store_msg v C s c r' M1 MSG_invalid_literal_lengths_set HM1 Hput')).
      assert (HM3 : LMEM v (mkW s' c' r') M3).
      { apply (LMEM_store_scalar v C s c' r' _ M2 8 _ HM2); [lia | cbn; lia | exact Hput' | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M2 (cv_S v) _ s BAD (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HRC3 : RETC v (mkW s' c' r') M3).
      { subst M3 M2. apply (RETC_other v C); [| clear - CS; lia | clear - CS; cbn; lia | unfold sep in CfS; clear - CfS CS; cbn; lia].
        apply (RETC_other v C); [| clear - CZP; lia | clear - CZP; cbn; lia | unfold sep in CfZ; clear - CfZ CZP; cbn; lia].
        exact (RETC_store v C s c r' M). }
      pose proof (icset_msg_facts c MSG_invalid_literal_lengths_set) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
      assert (HX3 : LX v (mkW s' c' r')).
      { apply (LX_step0 v s c r s' c' r' HX NH NB); subst s' c' r'; try reflexivity; [live_mode_tac | cbn; clear - HretB; lia | rewrite K11; unfold MSG_invalid_literal_lengths_set; lia]. }
      pose proof (is6_mode _ _ _ _ (lm_sc _ _ _ HM3)) as C8'. cbn [w_s] in C8'. replace (is_mode s') with BAD in C8' by (subst s'; destruct s; reflexivity).
      pose proof (lm_rod _ _ _ HM3) as Mrod3.
      symex_reg HR1 (31%bv : reg) as W31. change 18446744073709535436 with ((-16180) mod 2 ^ 64) in W31. rewrite zw_neg_mod in W31.
      symex_reg HR1 (1%bv : reg) as W1. symex_reg HR1 (10%bv : reg) as W10. symex_reg HR1 (11%bv : reg) as W11.
      symex_reg HR1 (29%bv : reg) as W29. symex_reg HR1 (26%bv : reg) as W27.
      j1011_symex ilS 12%nat [true] [RVal (ELit 16209); RVal (ELit (JT BAD))] (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals F0
        (mkst R1 (Z_to_bv 64 pc6_disp) M3 s6_rom) R' HR' Hfr Hms.
      all: try (lazymatch goal with |- getr _ ?n = zw _ => first [assumption | rewrite (Hfr1 n eq_refl); assumption] end).
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTC3" G end.
      exists R', M3, (arm6_pc BAD). split.
      { apply (msteps_trans _ _ (mkst R1 (Z_to_bv 64 pc6_disp) M3 s6_rom)); subst M3 M2 M1; [by_run Hms1 | by_run Hms]. }
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s'; apply same_blocks_mode |]].
      + split; [exact HM3|]. split; [exact HRC3|]. split; [exact HX3|].
        symex_reg HR' (9%bv : reg) as G8'.
        unfold LREG_arm. split; [| split; [| intros _; exact G8']].
        * unfold LFIX, INF_FRAME, A6_JTAB. regs_via Hfr; first [exact W1 | exact W10 | exact W11 | exact W31 | exact W29
             | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl), (Hfr1 n eq_refl); assumption end | match goal with |- ?G => idtac "LFIX2 LEFT" G end].
        * unfold LVARS; cbn [w_r]. subst r'. cbn. regs_via Hfr; first [exact W1 | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl), (Hfr1 n eq_refl); assumption end
             | symex_reg HR' (27%bv : reg) as G26'; exact G26' | match goal with |- ?G => idtac "LVARS2 LEFT" G end].
      + cbn [w_r]. subst r'. cbn [ir_put irset_ret]. subst M3 M2 M1.
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia].
  Qed.
End SegB.
End FXG.
End InflA_Codelens6.
Export InflA_Codelens6.

Module InflA_Codelens8.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S.Segs6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflDec6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflA_Dist3.
Import InflA_Cl1.InflArmLib6e.
Import InflA_Cl1.InflNeed6b.
Import InflA_ClS.InflA_CodelensS.
Import InflA_Cl1.InflA_Codelens2.
Import InflA_Cl1.InflA_Codelens3.
Import InflA_Cl1.InflA_Codelens4.
Import InflA_Cl1.InflA_Codelens4b.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Lemma body_post_rebase : forall v s c0 r0 c1 r1 M res R' M' pc',
  ir_put r0 = ir_put r1 -> body_post v (mkW s c1 r1) M res R' M' pc' -> body_post v (mkW s c0 r0) M res R' M' pc'.
Proof.
  intros v s c0 r0 c1 r1 M res R' M' pc' Hp H. destruct res as [[|] w'|w'|rc w']; cbn [body_post w_s w_r] in *; rewrite ?Hp; try exact H.
  - destruct H as [H1 H2]. split; [exact (arm_post_rebase v s c0 r0 c1 r1 _ _ _ _ _ Hp H1) | exact H2].
  - exact (arm_post_rebase v s c0 r0 c1 r1 _ _ _ _ _ Hp H).
Qed.

Section Full.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_cb HB := destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens).

  Lemma rep_leave_post : forall s c r r1 R2 M here n,
    is_mode s = CODELENS -> 16 <= code_val here ->
    n = (if code_val here =? 16 then 2 else if code_val here =? 17 then 3 else 7) ->
    NEEDBITS (code_bits here + n) (mkW s c r) = ALeave (mkW s c r1) ->
    same5 r r1 -> LMEM v (mkW s c r1) M -> LX v (mkW s c r) -> LREG_leave v (mkW s c r1) R2 ->
    body_post v (mkW s c r) M (cb_after here (mkW s c r)) R2 M pc6_leave.
  Proof.
    intros s c r r1 R2 M here n Hmode Hv Hn EN S5 HM1 HX HL1.
    rewrite (cb_rep_leave here s c r n _ Hv Hn EN).
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof HX as HX0. open_lx HX.
    cbn [body_post arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
    split; [exact HM1|]. split; [| split; [apply same_blocks_refl | exact HL1]].
    apply (LX_step0 v s c r s c r1 HX0 NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg].
  Qed.

  Lemma cl_rep17_full : forall s c r R M here,
    is_mode s = CODELENS -> cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    code_val here = 17 -> 1 <= code_bits here <= 15 -> code_bits here <= ir_bits r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> VREG v s r (code_bits here) 17 R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d7e8) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ body_post v (mkW s c r) M (cb_after here (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M here Hmode HB RI CI Hv Hhb Hbx HM HRC HX HV. pose proof HB as HB0. open_cb HB.
    pose proof RI as RI0. open_rinv RI. pose proof (ic_I0 _ C) as CI0. pose proof (ic_P0 _ C) as CP0. pose proof (ic_S _ C) as CS.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63) by (rewrite ELC; cbn [ctab6 codeptr_addr]; clear - CS; lia).
    assert (Hhv32 : 0 <= is_have s < 2 ^ 32) by (clear - Hhv Htot; lia).
    assert (Hnd32 : 0 <= is_nlen s < 2 ^ 31 /\ 0 <= is_ndist s < 2 ^ 31) by (clear - Hnl Hnd Htot; lia).
    set (hb := code_bits here) in *.
    destruct (cl_split17 v C s c r R M hb HB0 RI0 ltac:(lia) HV) as [R1 X].
    assert (TAIL : forall r2 R2, hb + 3 <= ir_bits r2 -> RINV (cv_NI v) (cv_NO v) r2 -> ir_put r2 = ir_put r ->
              LMEM v (mkW s c r2) M -> RETC v (mkW s c r2) M -> LX v (mkW s c r2) -> NJE v s (hb + 3) hb c r2 R2 ->
              exists R' M' pc', msteps s6_segs (mkst R2 (Z_to_bv 64 0x1d8b0) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
                /\ body_post v (mkW s c r2) M (let r3 := cdrop r2 hb in cb_fin s c (cdrop r3 3) 0 (3 + BITSv (ir_hold r3) 3)) R' M' pc').
    { intros r2 R2 Hb2 RI2 Hp2 HM2 HRC2 HX2 HJ2.
      destruct (cl_r17 v C s c r2 R2 M hb HB0 RI2 ltac:(lia) Hb2 HJ2) as (R3 & Hms3 & HK).
      pose proof RI2 as RI2'. unfold RINV in RI2'. destruct RI2' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rb2 & Rh2).
      pose proof (RINV_drop (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) r2 hb RI2 ltac:(lia)) as [EW1 RI3].
      pose proof (RINV_drop (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) _ 3 RI3 ltac:(cbn; lia)) as [EW2 RI4].
      cbv zeta. set (r4 := cdrop (cdrop r2 hb) 3) in *.
      assert (Er4 : r4 = irset_bits (irset_hold (irset_bits (irset_hold r2 (Z.shiftr (ir_hold r2) hb)) (ir_bits r2 - hb))
                                     (Z.shiftr (ir_hold (irset_bits (irset_hold r2 (Z.shiftr (ir_hold r2) hb)) (ir_bits r2 - hb))) 3))
                          (ir_bits (irset_bits (irset_hold r2 (Z.shiftr (ir_hold r2) hb)) (ir_bits r2 - hb)) - 3)).
      { subst r4. unfold cdrop. rewrite EW1. cbn [ir_bits ir_hold irset_bits irset_hold]. cbn [ir_bits ir_hold irset_bits irset_hold] in EW2. rewrite EW2. reflexivity. }
      assert (RI4' : RINV (cv_NI v) (cv_NO v) r4) by (rewrite Er4; exact RI4).
      assert (BB : 0 <= BITSv (ir_hold (cdrop r2 hb)) 3 < 8) by (apply BITSv_bound; lia).
      destruct (cl_tail v C s c r4 R3 M 0 (3 + BITSv (ir_hold (cdrop r2 hb)) 3) Hmode HK ltac:(clear - Hhv; lia) ltac:(clear - Hnl Hnd Htot; lia) Halen
                  ltac:(clear - BB; lia) ltac:(lia) Hlb HA RI4'
                  ltac:(apply (LMEM_regs v s c r2 c r4 M HM2); rewrite ?Er4; reflexivity)
                  ltac:(apply (RETC_regs v (mkW s c r2)); [exact HRC2 | rewrite Er4; reflexivity])
                  ltac:(apply (LX_step0 v s c r2 s c r4 HX2 NH NB); rewrite ?Er4; try reflexivity; [rewrite Hmode; live_mode_tac | | ]; pose proof HX2 as Y; open_lx Y; [exact Xret | exact Xmsg]))
        as (R' & M' & pc' & Hms4 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [exact Hms3 | exact Hms4]|].
      apply (body_post_rebase v s c r2 c r4); [rewrite Er4; reflexivity | exact HPOST]. }
    destruct (Z.leb_spec (hb + 3) (ir_bits r)) as [GE|LT]; destruct X as [Hms1 HJ1].
    - assert (EN : NEEDBITS (hb + 3) (mkW s c r) = ARun tt (mkW s c r)) by (unfold NEEDBITS; apply NEEDBITS_k_done; cbn; exact GE).
      rewrite (cb_rep17 here s c r c r Hv EN).
      destruct (TAIL r R1 GE RI0 eq_refl HM HRC HX HJ1) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact HPOST].
    - pose proof (need_loop_s v s (hb + 3) 0x1d804 0x1d8b0 (NJS v s (hb + 3) hb) (NJE v s (hb + 3) hb) C ltac:(lia)
                    (cn17_step_H v s C (hb + 3) hb ltac:(lia) ltac:(lia) Hhv32 Hnd32 Hlb HA)
                    (cn17_step_E v s C (hb + 3) hb ltac:(lia) ltac:(lia) Hhv32 Hnd32 Hlb HA)
                    (cn17_dry v s C (hb + 3) hb ltac:(lia) ltac:(lia) Hhv32 Hnd32 Hlb HA)
                    8%nat c r R1 M HM HRC HJ1 RI0 CI LT ltac:(cbn; clear - LT Rbits Hhb; lia)) as NL.
      change (NEEDBITS_k 8 (hb + 3)) with (NEEDBITS (hb + 3)) in NL.
      destruct (NEEDBITS (hb + 3) (mkW s c r)) as [[] w1 | w1 | rc w1] eqn:EN; [| | destruct NL].
      + destruct NL as (r1 & R2 & -> & Hms2 & HJE & RI1 & S5 & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
        rewrite (cb_rep17 here s c r c r1 Hv EN).
        assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [rewrite Hmode; live_mode_tac | exact Q3 | rewrite Q5; pose proof HX as Y; open_lx Y; exact Xret | pose proof HX as Y; open_lx Y; exact Xmsg]).
        destruct (TAIL r1 R2 (proj1 Hb1) RI1 Q1 HM1 HRC1 HX1 HJE) as (R' & M' & pc' & Hms3 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]]|].
        apply (body_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
      + destruct NL as (r1 & R2 & -> & Hms2 & HL1 & RI1 & S5 & Hz & Hb1 & HM1 & HRC1).
        exists R2, M, pc6_leave. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
        apply (rep_leave_post s c r r1 R2 M here 3 Hmode ltac:(lia) ltac:(rewrite Hv; reflexivity) EN S5 HM1 HX HL1).
  Qed.
  Lemma cl_rep18_full : forall s c r R M here,
    is_mode s = CODELENS -> cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    18 <= code_val here -> 1 <= code_bits here <= 15 -> code_bits here <= ir_bits r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> VREG v s r (code_bits here) (code_val here) R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d7e8) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ body_post v (mkW s c r) M (cb_after here (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M here Hmode HB RI CI Hv Hhb Hbx HM HRC HX HV. pose proof HB as HB0. open_cb HB.
    pose proof RI as RI0. open_rinv RI. pose proof (ic_I0 _ C) as CI0. pose proof (ic_P0 _ C) as CP0. pose proof (ic_S _ C) as CS.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63) by (rewrite ELC; cbn [ctab6 codeptr_addr]; clear - CS; lia).
    assert (Hhv32 : 0 <= is_have s < 2 ^ 32) by (clear - Hhv Htot; lia).
    assert (Hnd32 : 0 <= is_nlen s < 2 ^ 31 /\ 0 <= is_ndist s < 2 ^ 31) by (clear - Hnl Hnd Htot; lia).
    set (hb := code_bits here) in *.
    pose proof (code_val_range here) as Hvr.
    destruct (cl_split18 v C s c r R M hb (code_val here) HB0 RI0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HV) as [R1 X].
    assert (TAIL : forall r2 R2, hb + 7 <= ir_bits r2 -> RINV (cv_NI v) (cv_NO v) r2 -> ir_put r2 = ir_put r ->
              LMEM v (mkW s c r2) M -> RETC v (mkW s c r2) M -> LX v (mkW s c r2) -> NJE v s (hb + 7) hb c r2 R2 ->
              exists R' M' pc', msteps s6_segs (mkst R2 (Z_to_bv 64 0x1d910) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
                /\ body_post v (mkW s c r2) M (let r3 := cdrop r2 hb in cb_fin s c (cdrop r3 7) 0 (11 + BITSv (ir_hold r3) 7)) R' M' pc').
    { intros r2 R2 Hb2 RI2 Hp2 HM2 HRC2 HX2 HJ2.
      destruct (cl_r18 v C s c r2 R2 M hb HB0 RI2 ltac:(lia) Hb2 HJ2) as (R3 & Hms3 & HK).
      pose proof RI2 as RI2'. unfold RINV in RI2'. destruct RI2' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rb2 & Rh2).
      pose proof (RINV_drop (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) r2 hb RI2 ltac:(lia)) as [EW1 RI3].
      pose proof (RINV_drop (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) _ 7 RI3 ltac:(cbn; lia)) as [EW2 RI4].
      cbv zeta. set (r4 := cdrop (cdrop r2 hb) 7) in *.
      assert (Er4 : r4 = irset_bits (irset_hold (irset_bits (irset_hold r2 (Z.shiftr (ir_hold r2) hb)) (ir_bits r2 - hb))
                                     (Z.shiftr (ir_hold (irset_bits (irset_hold r2 (Z.shiftr (ir_hold r2) hb)) (ir_bits r2 - hb))) 7))
                          (ir_bits (irset_bits (irset_hold r2 (Z.shiftr (ir_hold r2) hb)) (ir_bits r2 - hb)) - 7)).
      { subst r4. unfold cdrop. rewrite EW1. cbn [ir_bits ir_hold irset_bits irset_hold]. cbn [ir_bits ir_hold irset_bits irset_hold] in EW2. rewrite EW2. reflexivity. }
      assert (RI4' : RINV (cv_NI v) (cv_NO v) r4) by (rewrite Er4; exact RI4).
      assert (BB : 0 <= BITSv (ir_hold (cdrop r2 hb)) 7 < 128) by (apply BITSv_bound; lia).
      destruct (cl_tail v C s c r4 R3 M 0 (11 + BITSv (ir_hold (cdrop r2 hb)) 7) Hmode HK ltac:(clear - Hhv; lia) ltac:(clear - Hnl Hnd Htot; lia) Halen
                  ltac:(clear - BB; lia) ltac:(lia) Hlb HA RI4'
                  ltac:(apply (LMEM_regs v s c r2 c r4 M HM2); rewrite ?Er4; reflexivity)
                  ltac:(apply (RETC_regs v (mkW s c r2)); [exact HRC2 | rewrite Er4; reflexivity])
                  ltac:(apply (LX_step0 v s c r2 s c r4 HX2 NH NB); rewrite ?Er4; try reflexivity; [rewrite Hmode; live_mode_tac | | ]; pose proof HX2 as Y; open_lx Y; [exact Xret | exact Xmsg]))
        as (R' & M' & pc' & Hms4 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [exact Hms3 | exact Hms4]|].
      apply (body_post_rebase v s c r2 c r4); [rewrite Er4; reflexivity | exact HPOST]. }
    destruct (Z.leb_spec (hb + 7) (ir_bits r)) as [GE|LT]; destruct X as [Hms1 HJ1].
    - assert (EN : NEEDBITS (hb + 7) (mkW s c r) = ARun tt (mkW s c r)) by (unfold NEEDBITS; apply NEEDBITS_k_done; cbn; exact GE).
      rewrite (cb_rep18 here s c r c r ltac:(lia) ltac:(lia) ltac:(lia) EN).
      destruct (TAIL r R1 GE RI0 eq_refl HM HRC HX HJ1) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact HPOST].
    - pose proof (need_loop_s v s (hb + 7) 0x1d87c 0x1d910 (NJS v s (hb + 7) hb) (NJE v s (hb + 7) hb) C ltac:(lia)
                    (cn18_step_H v s C (hb + 7) hb ltac:(lia) ltac:(lia) Hhv32 Hnd32 Hlb HA)
                    (cn18_step_E v s C (hb + 7) hb ltac:(lia) ltac:(lia) Hhv32 Hnd32 Hlb HA)
                    (cn18_dry v s C (hb + 7) hb ltac:(lia) ltac:(lia) Hhv32 Hnd32 Hlb HA)
                    8%nat c r R1 M HM HRC HJ1 RI0 CI LT ltac:(cbn; clear - LT Rbits Hhb; lia)) as NL.
      change (NEEDBITS_k 8 (hb + 7)) with (NEEDBITS (hb + 7)) in NL.
      destruct (NEEDBITS (hb + 7) (mkW s c r)) as [[] w1 | w1 | rc w1] eqn:EN; [| | destruct NL].
      + destruct NL as (r1 & R2 & -> & Hms2 & HJE & RI1 & S5 & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
        rewrite (cb_rep18 here s c r c r1 ltac:(lia) ltac:(lia) ltac:(lia) EN).
        assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [rewrite Hmode; live_mode_tac | exact Q3 | rewrite Q5; pose proof HX as Y; open_lx Y; exact Xret | pose proof HX as Y; open_lx Y; exact Xmsg]).
        destruct (TAIL r1 R2 (proj1 Hb1) RI1 Q1 HM1 HRC1 HX1 HJE) as (R' & M' & pc' & Hms3 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]]|].
        apply (body_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
      + destruct NL as (r1 & R2 & -> & Hms2 & HL1 & RI1 & S5 & Hz & Hb1 & HM1 & HRC1).
        exists R2, M, pc6_leave. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
        apply (rep_leave_post s c r r1 R2 M here 7 Hmode ltac:(lia) ltac:(replace (code_val here =? 16) with false by (symmetry; apply Z.eqb_neq; lia); replace (code_val here =? 17) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity) EN S5 HM1 HX HL1).
  Qed.
  Lemma cl_rep16_full : forall s c r R M here,
    is_mode s = CODELENS -> cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    code_val here = 16 -> 1 <= code_bits here <= 15 -> code_bits here <= ir_bits r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> VREG v s r (code_bits here) 16 R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d7e8) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ body_post v (mkW s c r) M (cb_after here (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M here Hmode HB RI CI Hv Hhb Hbx HM HRC HX HV. pose proof HB as HB0. open_cb HB.
    pose proof RI as RI0. open_rinv RI. pose proof (ic_I0 _ C) as CI0. pose proof (ic_P0 _ C) as CP0. pose proof (ic_S _ C) as CS.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63) by (rewrite ELC; cbn [ctab6 codeptr_addr]; clear - CS; lia).
    assert (Hhv32 : 0 <= is_have s < 2 ^ 32) by (clear - Hhv Htot; lia).
    assert (Hnd32 : 0 <= is_nlen s < 2 ^ 31 /\ 0 <= is_ndist s < 2 ^ 31) by (clear - Hnl Hnd Htot; lia).
    set (hb := code_bits here) in *.
    destruct (cl_split16 v C s c r R M hb HB0 RI0 ltac:(lia) HV) as [R1 X].
    assert (TAIL : forall r2 R2, hb + 2 <= ir_bits r2 -> RINV (cv_NI v) (cv_NO v) r2 -> ir_put r2 = ir_put r ->
              LMEM v (mkW s c r2) M -> RETC v (mkW s c r2) M -> LX v (mkW s c r2) -> NJE v s (hb + 2) hb c r2 R2 ->
              exists R' M' pc', msteps s6_segs (mkst R2 (Z_to_bv 64 0x1d8d4) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
                /\ body_post v (mkW s c r2) M (let r3 := cdrop r2 hb in
                     if is_have s =? 0 then ARun false (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_bit_length_repeat) r3)
                     else cb_fin s c (cdrop r3 2) (arr_get (is_lens s) (is_have s - 1)) (3 + BITSv (ir_hold r3) 2)) R' M' pc').
    { intros r2 R2 Hb2 RI2 Hp2 HM2 HRC2 HX2 HJ2.
      destruct (cl_r16 v C s c r2 R2 M hb Hmode HB0 RI2 ltac:(lia) Hb2 HM2 HRC2 HX2 HJ2) as (R3 & M3 & pc3 & Hms3 & HK).
      cbv zeta. cbv zeta in HK. destruct (Z.eqb_spec (is_have s) 0) as [H0|H0].
      { exists R3, M3, pc3. split; [exact Hms3 | exact HK]. }
      destruct HK as (-> & -> & HK).
      pose proof RI2 as RI2'. unfold RINV in RI2'. destruct RI2' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rb2 & Rh2).
      pose proof (RINV_drop (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) r2 hb RI2 ltac:(lia)) as [EW1 RI3].
      pose proof (RINV_drop (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) _ 2 RI3 ltac:(cbn; lia)) as [EW2 RI4].
      set (r4 := cdrop (cdrop r2 hb) 2) in *.
      assert (Er4 : r4 = irset_bits (irset_hold (irset_bits (irset_hold r2 (Z.shiftr (ir_hold r2) hb)) (ir_bits r2 - hb))
                                     (Z.shiftr (ir_hold (irset_bits (irset_hold r2 (Z.shiftr (ir_hold r2) hb)) (ir_bits r2 - hb))) 2))
                          (ir_bits (irset_bits (irset_hold r2 (Z.shiftr (ir_hold r2) hb)) (ir_bits r2 - hb)) - 2)).
      { subst r4. unfold cdrop. rewrite EW1. cbn [ir_bits ir_hold irset_bits irset_hold]. cbn [ir_bits ir_hold irset_bits irset_hold] in EW2. rewrite EW2. reflexivity. }
      assert (RI4' : RINV (cv_NI v) (cv_NO v) r4) by (rewrite Er4; exact RI4).
      assert (BB : 0 <= BITSv (ir_hold (cdrop r2 hb)) 2 < 4) by (apply BITSv_bound; lia).
      pose proof (Blens (is_have s - 1) ltac:(lia)) as Bprev.
      destruct (cl_tail v C s c r4 R3 M (arr_get (is_lens s) (is_have s - 1)) (3 + BITSv (ir_hold (cdrop r2 hb)) 2) Hmode HK ltac:(clear - Hhv; lia) ltac:(clear - Hnl Hnd Htot; lia) Halen
                  ltac:(clear - BB; lia) Bprev Hlb HA RI4'
                  ltac:(apply (LMEM_regs v s c r2 c r4 M HM2); rewrite ?Er4; reflexivity)
                  ltac:(apply (RETC_regs v (mkW s c r2)); [exact HRC2 | rewrite Er4; reflexivity])
                  ltac:(apply (LX_step0 v s c r2 s c r4 HX2 NH NB); rewrite ?Er4; try reflexivity; [rewrite Hmode; live_mode_tac | | ]; pose proof HX2 as Y; open_lx Y; [exact Xret | exact Xmsg]))
        as (R' & M' & pc' & Hms4 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [exact Hms3 | exact Hms4]|].
      apply (body_post_rebase v s c r2 c r4); [rewrite Er4; reflexivity | exact HPOST]. }
    destruct (Z.leb_spec (hb + 2) (ir_bits r)) as [GE|LT]; destruct X as [Hms1 HJ1].
    - assert (EN : NEEDBITS (hb + 2) (mkW s c r) = ARun tt (mkW s c r)) by (unfold NEEDBITS; apply NEEDBITS_k_done; cbn; exact GE).
      rewrite (cb_rep16 here s c r c r Hv EN).
      destruct (TAIL r R1 GE RI0 eq_refl HM HRC HX HJ1) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact HPOST].
    - pose proof (need_loop_s v s (hb + 2) 0x1d840 0x1d8d4 (NJS v s (hb + 2) hb) (NJE v s (hb + 2) hb) C ltac:(lia)
                    (cn16_step_H v s C (hb + 2) hb ltac:(lia) ltac:(lia) Hhv32 Hnd32 Hlb HA)
                    (cn16_step_E v s C (hb + 2) hb ltac:(lia) ltac:(lia) Hhv32 Hnd32 Hlb HA)
                    (cn16_dry v s C (hb + 2) hb ltac:(lia) ltac:(lia) Hhv32 Hnd32 Hlb HA)
                    8%nat c r R1 M HM HRC HJ1 RI0 CI LT ltac:(cbn; clear - LT Rbits Hhb; lia)) as NL.
      change (NEEDBITS_k 8 (hb + 2)) with (NEEDBITS (hb + 2)) in NL.
      destruct (NEEDBITS (hb + 2) (mkW s c r)) as [[] w1 | w1 | rc w1] eqn:EN; [| | destruct NL].
      + destruct NL as (r1 & R2 & -> & Hms2 & HJE & RI1 & S5 & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
        rewrite (cb_rep16 here s c r c r1 Hv EN).
        assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [rewrite Hmode; live_mode_tac | exact Q3 | rewrite Q5; pose proof HX as Y; open_lx Y; exact Xret | pose proof HX as Y; open_lx Y; exact Xmsg]).
        destruct (TAIL r1 R2 (proj1 Hb1) RI1 Q1 HM1 HRC1 HX1 HJE) as (R' & M' & pc' & Hms3 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]]|].
        apply (body_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
      + destruct NL as (r1 & R2 & -> & Hms2 & HL1 & RI1 & S5 & Hz & Hb1 & HM1 & HRC1).
        exists R2, M, pc6_leave. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
        apply (rep_leave_post s c r r1 R2 M here 2 Hmode ltac:(lia) ltac:(rewrite Hv; reflexivity) EN S5 HM1 HX HL1).
  Qed.
End Full.
End FXG.
End InflA_Codelens8.
Export InflA_Codelens8.

Module InflA_Codelens9.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S.Segs6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflDec6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflA_Dist3.
Import InflA_Cl1.InflArmLib6e.
Import InflA_Cl1.InflNeed6b.
Import InflA_ClS.InflA_CodelensS.
Import InflA_Cl1.InflA_Codelens1.
Import InflA_Cl1.InflA_Codelens2.
Import InflA_Cl1.InflA_Codelens3.
Import InflA_Cl1.InflA_Codelens4.
Import InflA_Cl1.InflA_Codelens4b.
Import InflA_Codelens8.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma cb_facts_of_pinv : forall v s c r,
  is_mode s = CODELENS -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> is_have s < is_nlen s + is_ndist s ->
  cb_facts v s /\ tab_ok CODES (cat (is_codes s) (CDyn 0)) (is_lenbits s) (is_next s) = true /\ is_next s <= 1444.
Proof.
  intros v s c r Hmode HP Hlt. open_pinv HP.
  destruct PS as (_ & _ & (Alens & Awork & Acodes) & _ & _ & QC & _). destruct (QC Hmode) as (QN & QD & QH & CT & QL15).
  unfold ctab_ok in CT. destruct (ctab_ok_cases _ _ _ _ CT) as (ELC & NX & TC).
  pose proof (tab_ok_root _ _ _ _ TC) as (Rt1 & _ & _).
  pose proof SR as X. unfold SRNGq in X. do 26 (destruct X as [_ X]). destruct X as ((BL & _ & _) & _).
  split; [| split; [exact TC | exact NX]].
  unfold cb_facts. repeat (split; [first [assumption | lia] |]). exact BL.
Qed.

Definition ilCP : cfg := ilSx [0x1d7b0; 0x1d760] [].

Section Body.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_cb HB := destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens).

  Lemma cl_join : forall s c r R M here,
    is_mode s = CODELENS -> cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    tab_ok CODES (cat (is_codes s) (CDyn 0)) (is_lenbits s) (is_next s) = true -> is_next s <= 1444 ->
    here = cat (is_codes s) (is_lencode s) (BITSv (ir_hold r) (is_lenbits s)) -> code_bits here <= ir_bits r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> JREG v s r (BITSv (ir_hold r) (is_lenbits s)) (code_bits here) R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d7b0) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ body_post v (mkW s c r) M (cb_after here (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M here Hmode HB RI CI TC NX Ehere Hhb HM HRC HX HJ. pose proof HB as HB0. open_cb HB.
    pose proof RI as RI0. unfold RINV in RI0. destruct RI0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rbits & Rhold).
    pose proof (BITSv_bound (ir_hold r) (is_lenbits s) ltac:(lia)) as HJ1.
    pose proof (tab_root_entry CODES _ _ _ (BITSv (ir_hold r) (is_lenbits s)) TC HJ1) as (HB1 & _ & _ & CASES).
    rewrite ELC in Ehere. rewrite <- Ehere in HB1, CASES.
    pose proof (ctab6_cells v s c r M (is_lencode s) C HM ltac:(rewrite ELC; cbn; lia)) as TAB. rewrite ELC in TAB. cbn [cext] in TAB.
    assert (Hidx : 0 <= BITSv (ir_hold r) (is_lenbits s) < cext (is_lencode s)) by (rewrite ELC; cbn [cext]; pose proof (tab_ok_root _ _ _ _ TC) as (_ & R2 & _); clear - HJ1 R2 NX; lia).
    assert (TAB' : cells s6_segs M (ctab6 v (is_lencode s)) 4 4 (cext (is_lencode s)) (cat (is_codes s) (is_lencode s))) by (rewrite ELC; cbn [cext]; exact TAB).
    assert (Ehere' : here = cat (is_codes s) (is_lencode s) (BITSv (ir_hold r) (is_lenbits s))) by (rewrite ELC; exact Ehere).
    pose proof (tab_ok_root _ _ _ _ TC) as (Rt1 & _ & _).
    assert (Bh : 1 <= code_bits here <= 15) by (clear - HB1 Rt1; lia).
    pose proof (code_val_range here) as Hvr.
    destruct (Z_lt_le_dec (code_val here) 16) as [V16|V16].
    - rewrite (cb_lit here s c r V16).
      exact (cl_lit v C s c r R M _ here Hmode HB0 RI TAB' Hidx Ehere' Hhb ltac:(lia) V16 HM HRC HX HJ).
    - destruct (cl_rep_pre v C s c r R M _ here HB0 RI TAB' Hidx Ehere' ltac:(lia) V16 HM HJ) as (R1 & Hms1 & HV).
      destruct (Z.eq_dec (code_val here) 16) as [E16|N16]; [| destruct (Z.eq_dec (code_val here) 17) as [E17|N17]].
      + rewrite E16 in HV. destruct (cl_rep16_full v C s c r R1 M here Hmode HB0 RI CI E16 ltac:(lia) Hhb HM HRC HX HV) as (R' & M' & pc' & Hms2 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact HPOST].
      + rewrite E17 in HV. destruct (cl_rep17_full v C s c r R1 M here Hmode HB0 RI CI E17 ltac:(lia) Hhb HM HRC HX HV) as (R' & M' & pc' & Hms2 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact HPOST].
      + destruct (cl_rep18_full v C s c r R1 M here Hmode HB0 RI CI ltac:(lia) ltac:(lia) Hhb HM HRC HX HV) as (R' & M' & pc' & Hms2 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact HPOST].
  Qed.

  Definition PREG (s : inflate_state) (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    BKc v s r R /\ getr R 13 = zw (is_have s) /\ getr R 23 = zw (ir_hold r) /\ getr R 24 = zw (ir_bits r) /\ getr R 18 = zw (ir_have r)
    /\ getr R 27 = zw (cv_I0 v + ir_next r) /\ getr R 6 = zw (ir_have r) /\ getr R 7 = zw (cv_I0 v + ir_next r).

  Definition ppins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (11, EVar 35%nat); (22, EAdd (EVar 33%nat) (ELit 168));
     (31, ELit (-16180)); (29, ELit 30); (25, ELit 0x12510); (20, ELit 16209);
     (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat); (23, EVar 40%nat); (24, EVar 41%nat);
     (18, EVar 36%nat); (27, EAdd (EVar 43%nat) (EVar 44%nat)); (6, EVar 36%nat); (7, EAdd (EVar 43%nat) (EVar 44%nat));
     (13, EVar 45%nat); (14, EVar 46%nat); (12, EVar 47%nat); (16, EVar 48%nat); (15, EVar 49%nat)].
  Definition pvb : list (nat * Z) :=
    [(45%nat, 512); (46%nat, 512); (47%nat, 512); (48%nat, 2 ^ 15); (49%nat, 2 ^ 63); (50%nat, 16)].

  Lemma cl_body : forall s c r R M,
    is_mode s = CODELENS -> cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    tab_ok CODES (cat (is_codes s) (CDyn 0)) (is_lenbits s) (is_next s) = true -> is_next s <= 1444 ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> PREG s c r R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d73c) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ body_post v (mkW s c r) M (codelens_body (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M Hmode HB RI CI TC NX HM HRC HX HP. pose proof HB as HB0. open_cb HB.
    destruct HP as ((HF & G18 & G1 & G14 & G12 & G16 & G15) & G13 & G22 & G23 & G9 & G26 & G6 & G7). open_fix HF.
    open_ictx C. open_lmem HM. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    pose proof (tab_ok_root _ _ _ _ TC) as (Rt1 & Rt2 & Rt3).
    assert (Hofs : cofs_ok (is_lencode s)) by (rewrite ELC; cbn; lia).
    assert (TD : tab_ok CODES (cat (is_codes s) (is_lencode s)) (is_lenbits s) (is_next s) = true) by (rewrite ELC; exact TC).
    assert (Hext : is_next s <= cext (is_lencode s)) by (rewrite ELC; cbn [cext]; lia).
    pose proof (ctab6_range v (is_lencode s) C Hofs) as [HA0 HA1].
    pose proof (ctab6_cells v s c r M (is_lencode s) C HM Hofs) as TAB.
    pose proof (ones_range15 (is_lenbits s) Rt1) as Hones.
    pose proof (BITSv_bound (ir_hold r) (is_lenbits s) ltac:(lia)) as HJ1.
    assert (Hhv32 : 0 <= is_have s < 2 ^ 32) by (clear - Hhv Htot; lia).
    assert (Hnd32 : 0 <= is_nlen s < 2 ^ 31 /\ 0 <= is_ndist s < 2 ^ 31) by (clear - Hnl Hnd Htot; lia).
    set (last := cent1 s (ir_hold r)).
    pose proof (tab_root_entry CODES _ _ _ (BITSv (ir_hold r) (is_lenbits s)) TD HJ1) as (HB1 & _). change (cat _ _ _) with last in HB1.
    pose proof (code_bits_range last) as Hcb.
    assert (ED1 : DECODE1 (is_lencode s) (is_lenbits s) (mkW s c r)
                  = if code_bits last <=? ir_bits r then ARun last (mkW s c r)
                    else (PULLBYTE ;; DECODE_k 7 (is_lencode s) (fun h => BITSv h (is_lenbits s)) code_bits)%am (mkW s c r)).
    { unfold DECODE1. rewrite DECODE_k_S. rewrite code_at_cat. reflexivity. }
    rewrite codelens_body_dec1, ED1.
    destruct (Z.leb_spec (code_bits last) (ir_bits r)) as [LE|GT].
    - arm_symexP (@nil (Z * expr)) ilCP 12%nat [true] [RVal (EVar 50%nat)] ppins pvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); code_bits last] NoVals F0
        (mkst R (Z_to_bv 64 0x1d73c) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: rewrite ?idx0_exec by (first [clear - Rhold64; lia | clear - Rt1; lia]).
      all: try (subst last; unfold cent1; tab_read TAB (BITSv (ir_hold r) (is_lenbits s)); clear - HJ1 Rt2 Hext; lia).
      all: try (generalize HJ1; clear - HA0 HA1 Rt2 Hext; intro; lia).
      assert (HJ : JREG v s r (BITSv (ir_hold r) (is_lenbits s)) (code_bits last) R1).
      { symex_reg HR1 (28%bv : reg) as Q28. rewrite idx0_exec in Q28 by (first [clear - Rhold64; lia | clear - Rt1; lia]).
        symex_reg HR1 (5%bv : reg) as Q5. symex_reg HR1 (17%bv : reg) as Q17. symex_reg HR1 (18%bv : reg) as Q24. symex_reg HR1 (27%bv : reg) as Q26.
        unfold JREG, BKc. repeat match goal with |- _ /\ _ => split end;
          first [ apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity
                | exact Q28 | exact Q5 | exact Q17 | exact Q24 | exact Q26
                | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); assumption end
                | match goal with |- ?G => idtac "JREG LEFT" G end ]. }
      destruct (cl_join s c r R1 M last Hmode HB0 RI0 CI' TC NX ltac:(subst last; unfold cent1; reflexivity) LE HM HRC HX HJ) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
    -
      arm_symexP (@nil (Z * expr)) ilCP 12%nat [false] [RVal (EVar 50%nat)] ppins pvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); code_bits last] NoVals F0
        (mkst R (Z_to_bv 64 0x1d73c) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: rewrite ?idx0_exec by (first [clear - Rhold64; lia | clear - Rt1; lia]).
      all: try (subst last; unfold cent1; tab_read TAB (BITSv (ir_hold r) (is_lenbits s)); clear - HJ1 Rt2 Hext; lia).
      all: try (generalize HJ1; clear - HA0 HA1 Rt2 Hext; intro; lia).
      all: match goal with |- ?G => idtac "LEFTBD2" G end.
      assert (HJS : CJS v s (ir_bits r) (ir_have r) (ir_next r) r R1).
      { symex_reg HR1 (17%bv : reg) as Q17. symex_reg HR1 (29%bv : reg) as Q29. symex_reg HR1 (18%bv : reg) as Q24. symex_reg HR1 (30%bv : reg) as Q30. symex_reg HR1 (27%bv : reg) as Q26.
        unfold CJS, CK, INF_FRAME. repeat match goal with |- _ /\ _ => split end;
          first [ exact Q17 | exact Q29 | exact Q24 | exact Q30 | exact Q26 | clear; lia | clear - Rbits; lia
                | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); assumption end
                | match goal with |- ?G => idtac "CJS LEFT" G end ]. }
      pose proof (dec_loop v s c (is_lencode s) (fun h => BITSv h (is_lenbits s)) code_bits 15 0x1d760 0x1d7b0
                    (CJS v s (ir_bits r) (ir_have r) (ir_next r)) (CJE v s (ir_bits r) (ir_have r) (ir_next r)) C ltac:(lia)
                    (fun h Hh => need1_bound CODES _ _ _ h TD Hh)
                    CI'
                    (cl_step_H v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 (is_next s) TD Hext Hofs CI' Hhv32 Hnd32)
                    (cl_step_E v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 (is_next s) TD Hext Hofs CI' Hhv32 Hnd32)
                    (cl_dry v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 (is_next s) TD Hext Hofs CI' Hhv32 Hnd32)
                    7%nat r R1 M HM HRC HJS RI0
                    ltac:(cbv beta; change (code_at s (is_lencode s) (BITSv (ir_hold r) (is_lenbits s))) with last; exact GT)
                    ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - Rbits; lia)) as NL.
      destruct ((PULLBYTE ;; DECODE_k 7 (is_lencode s) (fun h => BITSv h (is_lenbits s)) code_bits)%am (mkW s c r))
        as [last1 w1 | w1 | rc w1]; [| | destruct NL].
      + destruct NL as (r1 & R2 & -> & Hms2 & HJE & RI1 & S5 & Eh1 & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
        pose proof HX as HX0. open_lx HX0.
        assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg]).
        subst last1.
        assert (HJ : JREG v s r1 (BITSv (ir_hold r1) (is_lenbits s)) (code_bits (code_at s (is_lencode s) (BITSv (ir_hold r1) (is_lenbits s)))) R2).
        { pose proof HJE as X. unfold CJE, CK in X.
          destruct X as (((E2 & E25 & E10 & E11 & E1 & E31 & E21 & EJT & E3 & E4) & E19 & E18 & E13 & E14 & E12 & E8 & E6 & E7 & E16 & E15) & E23 & E24 & E26 & E17 & E29 & E28 & E5).
          unfold JREG, BKc, LFIX. repeat match goal with |- _ /\ _ => split end; assumption. }
        destruct (cl_join s c r1 R2 M _ Hmode HB0 RI1 CI' TC NX (code_at_cat s (is_lencode s) (BITSv (ir_hold r1) (is_lenbits s))) (proj1 Hb1) HM1 HRC1 HX1 HJ) as (R' & M' & pc' & Hms3 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [| eapply msteps_trans; [exact Hms2 | exact Hms3]]; by_run Hms1|].
        apply (body_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
      + destruct NL as (r1 & R2 & -> & Hms2 & HL1 & RI1 & S5 & Hz & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
        pose proof HX as HX0. open_lx HX0.
        exists R2, M, pc6_leave. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1|].
        cbn [body_post arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
        split; [exact HM1|]. split; [| split; [apply same_blocks_refl | exact HL1]].
        apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg].
  Qed.
End Body.
End FXG.
End InflA_Codelens9.
Export InflA_Codelens9.

