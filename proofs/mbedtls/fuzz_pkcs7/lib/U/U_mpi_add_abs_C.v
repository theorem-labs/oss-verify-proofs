(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiJourney.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_cmp U_mpi_add_abs_W.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_add_abs_C () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.XJ"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_add_abs_W.AA_FRAME"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limbs_val"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_add_abs_W.AA_VAL"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_add_abs_W.AA_POST"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.lt"].


(* [comment removed for export] *)
Lemma w32_incr : forall w : word, w32 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1))) = (w32 w + 1) mod 2^32.
Proof.
  intros w. rewrite Z_to_bv64_swrap32_mod32. rewrite bv_unsigned_sx32. fold (w32 w). apply sxz_add_mod32. apply w32_range.
Qed.

Lemma incr_mod64 : forall w : word, (bv_swrap 32 (bv_unsigned (sx32 w) + 1)) mod 2^64 = sxz ((w32 w + 1) mod 2^32).
Proof.
  intros w. rewrite swrap32_mod64. rewrite bv_unsigned_sx32. fold (w32 w). rewrite sxz_add_mod32 by apply w32_range. reflexivity.
Qed.

Lemma limb32_w32_nth : forall xs k w, nth_error xs k = Some w -> limb32 xs k = w32 w.
Proof. intros xs k w H. unfold limb32, w32. erewrite nth_error_nth by exact H. reflexivity. Qed.

Lemma sxz_ge1_iff : forall u, 0 <= u < 2^32 -> (1 <= sxz u <-> u <> 0).
Proof. intros u Hu. unfold sxz. destruct (Z.ltb_spec u (2^31)); lia. Qed.

(* [comment removed for export] *)
Section C.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (dA dB : mpd) (lo : Z) (MSF : Z)
            (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Hypothesis MSFE : MSF = U_MEMSET_FUNC.
  Hypothesis CA : const_at L MSF 8.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 176 - hl_stack L.
  Local Notation FRAME := (AA_FRAME ra s0 s1 s2 s3 s4 s5 s6).
  Local Notation POST := (AA_POST L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dA dB lo X sX nX pX xs0 padX ownX).
  Local Notation VAL := (AA_VAL dA dB).
  Hypothesis JCX : JC usegs L HI h LB m mo dX sp lo 64 FRAME.

  Local Ltac jc_open := pose proof JCX as [HLS SW DIMG HND ROIMG DHI HH MX NST XW XLS ACL FS0 SLO HTOP FSZ].
  Local Notation XJ0 := (XJ usegs L HI h LB m mo dX sp lo 64 FRAME []).
  Local Ltac xj_open J := pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1]; cbn [app] in HH1.
  Local Ltac chk_lia K :=
    exfalso; rewrite ?zb_lxor_ones in K by lia;
    repeat match type of K with context [bv_unsigned (Z_to_bv 64 ?z)] =>
      first [rewrite (unsigned_lit z) in K by lia
            | let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 z)) in change (bv_unsigned (Z_to_bv 64 z)) with v in K] end;
    lia.
  Local Ltac land3_chk H :=
    lazymatch goal with |- context [Z.land ?p 3] =>
      let E := fresh "E" in
      assert (E : Z.land p 3 = 0)
        by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; clear - H; Z.div_mod_to_equations; lia);
      rewrite E; clear E end.

  #[using="HFREE HCALLOC MSF MSFE CA TP SPA SLO2 JCX"] Lemma add_LOOP :
    forall (k : nat) (t0 t1 t2 raj a0 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 r1 ra1 r2 r4 r5 : word) (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model)
      (xs : list word) (pXc N J : Z),
    N - J <= Z.of_nat k ->
    XJ usegs L HI h LB m mo dX sp lo 64 FRAME [] hc LBc mc moc (mkMPD X 1 N pXc xs padX LHeap) ->
    1 <= J <= N -> limbs_val xs + 2 ^ (32 * J) = VAL ->
    r1 = Z_to_bv 64 (J - 1) -> ra1 = Z_to_bv 64 (pXc + 4 * J - 4) -> r2 = Z_to_bv 64 (-5) -> r4 = Z_to_bv 64 9998 -> r5 = Z_to_bv 64 (4 * J) ->
    aevtM usegs moc POST (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 X) r1 a0 ra1 a2 a3 a4 a5 a6 a7
      r2 (Z_to_bv 64 N) r4 r5 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x206bc) fc None mc (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros until J; intros Hk J0 HJ HV -> -> -> -> ->.
    all: jc_open; pose proof (bv_unsigned_in_range 64 sp) as SPB; change (bv_modulus 64) with (2^64) in SPB; pose proof alloc_ceiling_pos as ACP.
    all: pose proof alloc_ceiling_bounds as ACV.
    all: pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J0) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1); cbn [app] in HBR1, HAP1, ND1.
    all: cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    all: ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & ARR1 & P0 & PC & PI).
    all: pose proof J0 as JX; xj_open JX; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    all: pose proof (munch_refl [(pXc, pXc + 4 * N)] mc) as MU; pose proof (wmono_refl usegs mc) as WM.
    all: zstep; zstep; if_cases K0; zify_cond K0.
    all: swap 1 2.
    - exfalso. clear - K0 Hk HJ. lia.
    - zstep. if_cases K1; zify_cond K1.
      { eapply add_retm16; [exact JCX| exact J0]. }
      assert (EJ : J = N) by (clear - K0 HJ; lia). subst J.
      try replace (N - 1 + 1) with N by lia.
      eapply add_G2; [exact HFREE| exact HCALLOC| exact MSFE| exact CA| exact TP| exact SPA| exact SLO2| exact JCX| exact J0| clear - K1; lia| exact HV].
    - zstep. if_cases K1; zify_cond K1.
      { eapply add_retm16; [exact JCX| exact J0]. }
      assert (EJ : J = N) by (clear - K0 HJ; lia). subst J.
      try replace (N - 1 + 1) with N by lia.
      eapply add_G2; [exact HFREE| exact HCALLOC| exact MSFE| exact CA| exact TP| exact SPA| exact SLO2| exact JCX| exact J0| clear - K1; lia| exact HV].
    - zstep. zstep. zstep. land3_chk XPAL. zstep. if_false.
      destruct (nth_error xs (Z.to_nat J)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LEN1 K0 HJ; lia].
      pose proof (u32arr_read usegs mc pXc xs J w _ ARR1 NTH ltac:(clear - HJ; lia) eq_refl) as RD.
      zstep. clear RD. zstep.
      pose proof (u32arr_store_ok usegs mc pXc xs J _ ARR1 ltac:(clear - HJ K0 LEN1; lia) eq_refl) as SOK.
      zstep.
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
        pose proof (u32arr_write usegs mc pXc xs J v ARR1 ltac:(clear - HJ K0 LEN1; lia)) as ARR2 end.
      clear ARR1 MX1 HH1 SOK1 HPX1 FR1.
      store_done.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      zstep; if_cases KH; zify_cond KH; [chk_lia KH|].
      match goal with ST2 : stk usegs m2 _ _, MI2 : mem_inv usegs m2 |- _ =>
        pose proof (xj_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ _ _ J0 MU WM MI2 ST2
                      ltac:(intros a NO; left; destruct (outside_dec [(pXc, pXc + 4 * N)] a) as [O|O]; [exfalso; exact (NO O)| cbn in O; clear - O; lia])
                      ltac:(cbn; clear - PC ACL SLO HLS; lia) ltac:(cbn; pose proof (XP1 eq_refl); clear - H; lia) ARR2
                      ltac:(rewrite upd_length; reflexivity)) as J2 end.
      pose proof (limb32_w32_nth xs (Z.to_nat J) w NTH) as LW. pose proof (w32_range w) as WR.
      assert (LVU : limbs_val (upd xs (Z.to_nat J) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1))))
                    = limbs_val xs + 2 ^ (32 * J) * ((w32 w + 1) mod 2 ^ 32 - w32 w)).
      { rewrite limbs_val_upd by (clear - HJ K0 LEN1; lia). fold (w32 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1)))).
        rewrite w32_incr, LW. replace (Z.of_nat (Z.to_nat J)) with J by (clear - HJ; lia). reflexivity. }
      zstep. zstep. zstep. zstep. if_cases KB; zify_cond KB; rewrite incr_mod64 in KB.
      + apply (proj1 (sxz_zero_iff _ ltac:(clear; apply Z.mod_pos_bound; lia))) in KB.
        eapply IH with (N := N) (J := J + 1);
          [clear - Hk K0; lia| exact J2| clear - HJ K0; lia| | f_equal; clear; lia| f_equal; clear; lia| apply bv_eq; reflexivity| apply bv_eq; reflexivity| f_equal; clear; lia].
        rewrite LVU, KB. replace (32 * (J + 1)) with (32 * J + 32) by (clear; lia). rewrite Z.pow_add_r by (clear - HJ; lia).
        assert (w32 w = 2 ^ 32 - 1) by (clear - KB WR; lia). clear - HV H. nia.
      + assert (NZ : (w32 w + 1) mod 2 ^ 32 <> 0) by (intros E; apply KB; rewrite E; reflexivity).
        zstep.
        eapply add_ret; [exact JCX| exact J2|]. left. split; [reflexivity|]. split; [| reflexivity].
        unfold mpd_val. cbn [md_sg md_limbs]. rewrite LVU. rewrite Z.mod_small by (clear - WR NZ; lia). clear - HV. lia.
  Qed.

  #[using="HFREE HCALLOC MSF MSFE CA TP SPA SLO2 JCX"] Lemma add_ITER1 :
    forall (t0 t1 t2 raj a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 : word) (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model)
      (xs : list word) (pXc N j : Z),
    XJ usegs L HI h LB m mo dX sp lo 64 FRAME [] hc LBc mc moc (mkMPD X 1 N pXc xs padX LHeap) ->
    1 <= j < N -> limbs_val xs + 2 ^ (32 * j) = VAL ->
    aevtM usegs moc POST (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 j) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (j + 1)) (Z_to_bv 64 N) (Z_to_bv 64 pXc) (Z_to_bv 64 (4 * j + 4)) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20688) fc None mc (seg_rom usegs)).
  Proof.
    intros until j; intros J0 HJ HV.
    jc_open; pose proof (bv_unsigned_in_range 64 sp) as SPB; change (bv_modulus 64) with (2^64) in SPB; pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J0) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1); cbn [app] in HBR1, HAP1, ND1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & ARR1 & P0 & PC & PI).
    pose proof J0 as JX; xj_open JX; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    clear MX1 HH1 SOK1 HPX1 FR1.
    pose proof (munch_refl [(pXc, pXc + 4 * N)] mc) as MU; pose proof (wmono_refl usegs mc) as WM.
    zstep. zstep. zstep. land3_chk XPAL. zstep. if_false.
    destruct (nth_error xs (Z.to_nat j)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LEN1 HJ; lia].
    pose proof (u32arr_read usegs mc pXc xs j w _ ARR1 NTH ltac:(clear - HJ; lia) eq_refl) as RD.
    zstep. clear RD. zstep. zstep.
    pose proof (u32arr_store_ok usegs mc pXc xs j _ ARR1 ltac:(clear - HJ LEN1; lia) eq_refl) as SOK.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
      pose proof (u32arr_write usegs mc pXc xs j v ARR1 ltac:(clear - HJ LEN1; lia)) as ARR2 end.
    clear ARR1. store_done.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    zstep; if_cases KH; zify_cond KH; [chk_lia KH|].
    match goal with ST2 : stk usegs m2 _ _, MI2 : mem_inv usegs m2 |- _ =>
      pose proof (xj_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ _ _ J0 MU WM MI2 ST2
                    ltac:(intros a NO; left; destruct (outside_dec [(pXc, pXc + 4 * N)] a) as [O|O]; [exfalso; exact (NO O)| cbn in O; clear - O; lia])
                    ltac:(cbn; clear - PC ACL SLO HLS; lia) ltac:(cbn; pose proof (XP1 eq_refl); clear - H; lia) ARR2
                    ltac:(rewrite upd_length; reflexivity)) as J2 end.
    pose proof (limb32_w32_nth xs (Z.to_nat j) w NTH) as LW. pose proof (w32_range w) as WR.
    assert (LVU : limbs_val (upd xs (Z.to_nat j) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1))))
                  = limbs_val xs + 2 ^ (32 * j) * ((w32 w + 1) mod 2 ^ 32 - w32 w)).
    { rewrite limbs_val_upd by (clear - HJ LEN1; lia). fold (w32 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1)))).
      rewrite w32_incr, LW. replace (Z.of_nat (Z.to_nat j)) with j by (clear - HJ; lia). reflexivity. }
    pose proof (sxz_range ((w32 w + 1) mod 2 ^ 32) ltac:(clear; apply Z.mod_pos_bound; lia)) as SXR.
    zstep. if_cases KB; zify_cond KB; rewrite incr_mod64 in KB.
    - assert (NZ : (w32 w + 1) mod 2 ^ 32 <> 0) by (intros E; rewrite E in KB; change (sxz 0) with 0 in KB; clear - KB; lia).
      eapply add_ret0; [exact JCX| exact J2| | reflexivity].
      unfold mpd_val. cbn [md_sg md_limbs]. rewrite LVU. rewrite Z.mod_small by (clear - WR NZ; lia). clear - HV. lia.
    - assert (Z0 : (w32 w + 1) mod 2 ^ 32 = 0)
        by (apply (proj1 (sxz_zero_iff _ ltac:(clear; apply Z.mod_pos_bound; lia))); clear - KB SXR; lia).
      zstep. zstep. zstep.
      eapply (add_LOOP (Z.to_nat (N - (j + 1)))) with (N := N) (J := j + 1);
        [clear - HJ; lia| exact J2| clear - HJ; lia| | f_equal; clear; lia| f_equal; clear; lia| apply bv_eq; reflexivity| apply bv_eq; reflexivity| f_equal; clear; lia].
      rewrite LVU. replace (32 * (j + 1)) with (32 * j + 32) by (clear; lia). rewrite Z.pow_add_r by (clear - HJ; lia).
      assert (w32 w = 2 ^ 32 - 1) by (clear - Z0 WR; lia). clear - HV H Z0. nia.
  Qed.

  #[using="HFREE HCALLOC MSF MSFE CA TP SPA SLO2 JCX"] Lemma add_FIRST :
    forall (t0 t1 t2 raj a1 a2 a3 a4 a5 a6 a7 x19 x22 t3 t4 t5 t6 : word) (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model)
      (xs : list word) (pXc N j c : Z),
    XJ usegs L HI h LB m mo dX sp lo 64 FRAME [] hc LBc mc moc (mkMPD X 1 N pXc xs padX LHeap) ->
    1 <= j <= N -> 0 <= c <= 1 -> limbs_val xs + c * 2 ^ (32 * j) = VAL ->
    aevtM usegs moc POST (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 j) (Z_to_bv 64 c) a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (j + 1)) x19 (Z_to_bv 64 pXc) (Z_to_bv 64 (4 * j + 4)) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x205e4) fc None mc (seg_rom usegs)).
  Proof.
    intros until c; intros J0 HJ HC HV.
    jc_open; pose proof (bv_unsigned_in_range 64 sp) as SPB; change (bv_modulus 64) with (2^64) in SPB; pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J0) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1); cbn [app] in HBR1, HAP1, ND1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & ARR1 & P0 & PC & PI).
    pose proof J0 as JX; xj_open JX; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    pose proof MX1 as [(CX1 & _) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1. unfold mpi_cells in CX1.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl usegs mc) as WM.
    zstep. zstep. zstep; if_cases KC1; zify_cond KC1; [chk_lia KC1|].
    zstep; if_cases KC2; zify_cond KC2; [chk_lia KC2|].
    zstep. zstep. zstep; if_cases KC3; zify_cond KC3; [chk_lia KC3|].
    zstep. if_cases K0; zify_cond K0.
    { assert (c = 0) as -> by (clear - K0 HC; lia).
      eapply add_ret; [exact JCX| exact J0|]. left. split; [reflexivity|]. split; [| reflexivity]. unfold mpd_val. cbn [md_sg md_limbs]. clear - HV. lia. }
    assert (c = 1) as -> by (clear - K0 HC; lia).
    zstep. rewrite zx16_small by (clear - NR1; lia). zstep. if_cases K1; zify_cond K1.
    - eapply add_ITER1; [exact J0| clear - K1 HJ; lia| clear - HV; lia].
    - assert (EJ : j = N) by (clear - K1 HJ; lia). subst j.
      zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
      { eapply add_retm16; [exact JCX| exact J0]. }
      eapply add_G3; [exact HFREE| exact HCALLOC| exact MSFE| exact CA| exact TP| exact SPA| exact SLO2| exact JCX| exact J0| clear - K2 NR1 N1; lia| clear - HV; lia].
  Qed.
End C.
