(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux X509Aux MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_pk_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_pk_info () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "stdpp.bitvector.definitions.Z_to_bv"; "pk_info_of"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "pk_info_from_type_post"; "Stdlib.ZArith.BinInt.Z.pow"].


Definition U_PK_INFO_FROM_TYPE : Z := 0x29c88.
Definition U_PK_INFO_TBL : Z := 0x48cf8.
Definition U_PK_INFOS : list Z := [U_RSA_INFO; U_ECKEY_INFO; U_ECKEYDH_INFO; U_ECDSA_INFO].

Definition pk_info_of (INFOS : list Z) (t : Z) : Z :=
  if (1 <=? t) && (t <=? 4) then nth (Z.to_nat (t - 1)) INFOS 0 else 0.

Definition pk_info_from_type_post (segs : list Segment) (INFOS : list Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (t : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_info ()) "Lms',$0.(1.(2.&40.)La0',(2.&40.)(1.(2.&40.)La1,(2.&40.)(3.(4.$0.R3.(5.(6.O21.O20.O1?.O1>.O1=.O1<.O1;.O1:.O19.R2.R1.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.)O4.(7.O21.)O3.(8.(2.&40.))O1.(9.O23.)))(4.(2.&40.)R2.(:.&40.(;.O22.O2.))))))")
(* [comment removed for export] *).

Definition pk_info_from_type_stmt (segs : list Segment) (L : heap_layout) (TBL : Z) (INFOS : list Z) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_info ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(=.(2.&8.))P,(>.O5.R1.)P,(?.O5.O4.R2.)P,(10.O4.O3.+20.)P,(4.$11.(12.(13.&40.R25.)+2.)=)(14.O5.(15.O5.O2.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.(12.(13.&40.R1=.)(16.+2.+20.))R5.)(5.(6.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)R7.(:.&40.O1.)R6.(8.(2.&40.))R5.(9.O5.)))")
(* [comment removed for export] *).

Lemma pk_info_of_in : forall INFOS t, pk_info_of INFOS t = 0 \/ In (pk_info_of INFOS t) INFOS.
Proof.
  intros INFOS t. unfold pk_info_of. destruct ((1 <=? t) && (t <=? 4)); [| left; reflexivity].
  destruct (nth_in_or_default (Z.to_nat (t - 1)) INFOS 0) as [H|H]; [right; exact H| left; exact H].
Qed.

Section Walk.
  Variable L : heap_layout.
  Hypothesis CA_TBL : const_at L U_PK_INFO_TBL 32.

  #[using="CA_TBL"] Lemma U_pk_info_from_type_spec : pk_info_from_type_stmt usegs L U_PK_INFO_TBL U_PK_INFOS U_PK_INFO_FROM_TYPE.
  Proof.
    unfold pk_info_from_type_stmt, U_PK_INFO_FROM_TYPE. intros until m. intros MI SOK _ RA.
    pose proof (bv_unsigned_in_range 64 a0) as AR. change (bv_modulus 64) with (2^64) in AR.
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    assert (CAk : forall k, 0 <= k <= 3 -> const_at L (U_PK_INFO_TBL + 8 * k) 8).
    { intros k Hk. ddestruct CA_TBL as (C1 & C2 & C3). split; [lia|]. split; [lia|]. intros a Ha. apply C3. lia. }
    let tbl_entry k TB :=
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        let a := eval vm_compute in (U_PK_INFO_TBL + 8 * k) in
        let bs := eval vm_compute in (match image_bytes usegs a 8 with Some bs => bs | None => [] end) in
        pose proof (statics_ok_cells usegs L mx a bs SOK (CAk k ltac:(lia)) ltac:(vm_compute; reflexivity)) as TB;
        cbn [length] in TB end in
    tbl_entry 0 TE0; tbl_entry 1 TE1; tbl_entry 2 TE2; tbl_entry 3 TE3.
    zstep. zstep. zstep. if_cases K; zify_cond K; set (z := bv_unsigned a0) in *;
      pose proof (bv_swrap_in_range 32 (z + -1) ltac:(discriminate)) as SR; unfold bv_half_modulus in SR;
      replace (bv_modulus 32 `div` 2) with (2^31) in SR by reflexivity;
      pose proof (swrap32_mod64 (z + -1)) as SM; unfold sxz in SM; change (2^64) with 18446744073709551616 in SM; change (2^32) with 4294967296 in SM;
      pose proof (Z.mod_pos_bound z 4294967296 ltac:(lia)) as TR; pose proof (Z.mod_pos_bound (z + -1) 4294967296 ltac:(lia)) as TR1;
      change (2^32) with 4294967296.
    - (* [comment removed for export] *)
      zstep. zstep. fin.
      unfold pk_info_of.
      destruct (Z.leb_spec 1 (z mod 4294967296)) as [H1|H1]; [destruct (Z.leb_spec (z mod 4294967296) 4) as [H2|H2]|]; cbn [andb]; try reflexivity.
      exfalso. clear -K H1 H2 AR SR SM TR TR1.
      destruct (Z.ltb_spec ((z + -1) mod 4294967296) (2^31)) as [LT|GE]; [| lia].
      assert (E1 : (z + -1) mod 4294967296 = z mod 4294967296 - 1).
      { replace (z + -1) with (z mod 4294967296 - 1 + (z / 4294967296) * 4294967296) by (pose proof (Z.div_mod z 4294967296 ltac:(lia)); lia). rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
      lia.
    - (* [comment removed for export] *)
      set (sw := bv_swrap 32 (z + -1)) in *.
      assert (SW03 : 0 <= sw <= 3) by (clear -K SR; lia).
      assert (ET : z mod 4294967296 = sw + 1).
      { clear -K SR SM TR TR1 SW03 AR. destruct (Z.ltb_spec ((z + -1) mod 4294967296) (2^31)) as [LT|GE]; [| lia].
        assert (E2 : (z + -1) mod 4294967296 = sw) by lia.
        replace z with ((z + -1) mod 4294967296 + 1 + ((z + -1) / 4294967296) * 4294967296) by (pose proof (Z.div_mod (z + -1) 4294967296 ltac:(lia)); lia).
        rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia. }
      assert (SWM : sw mod 18446744073709551616 = sw) by (apply Z.mod_small; clear -SW03; lia).
      rewrite SWM in *.
      assert (SW4 : sw = 0 \/ sw = 1 \/ sw = 2 \/ sw = 3) by (clear -SW03; lia).
      clearbody sw. clear K SR SM TR TR1 SW03 SWM.
      destruct SW4 as [->|[->|[->| ->]]];
        (zstep; zstep; zstep; zstep; zstep; zstep; fin; unfold pk_info_of; rewrite ET; reflexivity).
  Qed.
End Walk.
