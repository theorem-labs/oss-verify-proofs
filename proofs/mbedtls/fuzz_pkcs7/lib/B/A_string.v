(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_string.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require HA_F_memcpy HA_F_memset.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_string () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Peano.ge"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Lists.ListDef.firstn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.P.P_string.memcmp_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Lemma A_memcpy_spec : memcpy_stmt asegs 0x0ea9c0.
Proof. exact HA_F_memcpy.memcpy_spec. Qed.

Lemma A_memset_spec : memset_stmt asegs 0x0eadc4.
Proof. exact HA_F_memset.memset_spec. Qed.
(* [comment removed for export] *)

Lemma firstn_S_nth {A} (l : list A) i x : nth_error l i = Some x -> firstn (S i) l = firstn i l ++ [x].
Proof.
  revert i. induction l as [|a l IH]; intros [|i] H; cbn in H; try discriminate.
  - injection H as ->. reflexivity.
  - cbn. f_equal. apply IH. exact H.
Qed.

Section Memcmp.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).

  (* [comment removed for export] *)
  #[using="Type"] Lemma memcmp_loop : ltac2:(CDefT.buildp (gd_tbl_A_string ()) "Pk,$0.PP0,$1.PQ0,$1.Pxs0,(2.(3.&8.))Pys0,(2.(3.&8.))Pp,$1.Pq,$1.Pa3,(3.&40.)Pa4,(3.&40.)P,(4.$5.Vm,R8.R6.)P,(4.$5.Vm,R8.R6.)P,(6.$0.(7.(3.&8.)R8.)(7.(3.&8.)R7.))P,(8.R;.R7.)P,(8.R;.R7.)P,(6.$1.(9.R9.R=.)(9.R8.R<.))P,(:.R?.#1.)P,(6.$1.(;.R10.)(9.(;.(7.(3.&8.)R=.))(9.R;.R?.)))P,(6.(2.(3.&8.))(<.(3.&8.)(=.(9.R<.R10.))R>.)(<.(3.&8.)(=.(9.R;.R?.))R=.))(>.$5.(?.$5.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,Va5,Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,VF,Vfc,R?.R>.Vm,)(10.(11.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(12.&40.R=.)(12.&40.R<.)(12.&40.(;.R12.))R;.R:.Va5,Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(12.&40.+>:994.)Vfc,(13.(3.&40.))Vm,(14.$5.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros P0 Q0 xs0 ys0 p q a3 a4 HX HY HL HP HQ HD Hk HK HF; [lia|].
    dpose HX as (X0 & X1 & _). dpose HY as (Y0 & Y1 & _).
    destruct (nth_error xs0 (Z.to_nat (p - P0))) as [x|] eqn:NX; [| apply nth_error_None in NX; lia].
    destruct (nth_error ys0 (Z.to_nat (q - Q0))) as [y|] eqn:NY; [| apply nth_error_None in NY; lia].
    pose proof (u8ro_read asegs m P0 xs0 (p - P0) x _ HX NX ltac:(lia) eq_refl) as RDX.
    pose proof (u8ro_read asegs m Q0 ys0 (q - Q0) y _ HY NY ltac:(lia) eq_refl) as RDY.
    pose proof (bv_unsigned_in_range 8 x) as XR. pose proof (bv_unsigned_in_range 8 y) as YR. unfold bv_modulus in XR, YR. cbn in XR, YR.
    zstep. zstep. zstep.
    if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KE by lia.
      zstep. zstep. apply evt_done. unfold memcmp_post. deexists 5. exists (bv_unsigned x - bv_unsigned y).
      split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
      split; [intros E; exfalso|intros E; exfalso].
      + apply KE. f_equal. lia.
      + subst ys0. rewrite <- HD in NY. replace (Z.to_nat (q - Q0)) with (Z.to_nat (p - P0)) in NY by lia. rewrite NX in NY. injection NY as ->. apply KE. reflexivity.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KE by lia.
      assert (EXY : x = y) by (apply bv_eq; lia).
      zstep. zstep. zstep. zstep.
      if_cases KZ; zify_cond KZ.
      + (* [comment removed for export] *)
        rewrite ?unsigned_lit in KZ by lia.
        replace (Z_to_bv 64 (Z.of_nat (S k) + -1)) with (Z_to_bv 64 (Z.of_nat k)) by (f_equal; lia).
        eapply (IH P0 Q0 xs0 ys0 (p + 1) (q + 1)); try eassumption; try lia.
        replace (Z.to_nat (p + 1 - P0)) with (S (Z.to_nat (p - P0))) by lia.
        replace (Z.to_nat (q + 1 - Q0)) with (S (Z.to_nat (q - Q0))) by lia.
        rewrite (firstn_S_nth xs0 _ x NX), (firstn_S_nth ys0 _ y NY), HF, EXY. reflexivity.
      + (* [comment removed for export] *)
        rewrite ?unsigned_lit in KZ by lia.
        zstep. zstep. apply evt_done. unfold memcmp_post. deexists 5. exists 0.
        split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros _|intros _; reflexivity].
        assert (LX : length xs0 = S (Z.to_nat (p - P0))) by lia.
        assert (LY : length ys0 = S (Z.to_nat (q - Q0))) by lia.
        rewrite <- (firstn_all xs0), <- (firstn_all ys0), LX, LY.
        rewrite (firstn_S_nth xs0 _ x NX), (firstn_S_nth ys0 _ y NY), HF, EXY. reflexivity.
  Qed.
End Memcmp.

Lemma memcmp_entry_walk (ENTRY : Z) :
  ENTRY = 0x0ea990 -> memcmp_stmt asegs ENTRY.
Proof.
  intros HE. intros until ys. intros HX HY LX LY.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. pose proof (bv_unsigned_in_range 64 a2) as R2.
  unfold bv_modulus in R0, R1, R2. cbn in R0, R1, R2.
  assert (J : evt asegs (memcmp_post asegs ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc xs ys m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x0ea990) fc None m (seg_rom asegs))).
  { zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *) zstep. zstep. apply evt_done. unfold memcmp_post. deexists 5. exists 0.
      split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros _|reflexivity].
      destruct xs; [|cbn in LX; lia]. destruct ys; [reflexivity|cbn in LY; lia].
    - rewrite <- (Z_to_bv_bv_unsigned a0), <- (Z_to_bv_bv_unsigned a1), <- (Z_to_bv_bv_unsigned a2).
      replace (bv_unsigned a2) with (Z.of_nat (length xs)) by lia.
      eapply (memcmp_loop ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                (length xs) (bv_unsigned a0) (bv_unsigned a1) xs ys); try eassumption; try lia.
      rewrite !Z.sub_diag. reflexivity. }
  rewrite HE. exact J.
Qed.

Lemma A_memcmp_spec : memcmp_stmt asegs 0x0ea990.
Proof. apply memcmp_entry_walk. reflexivity. Qed.

(* [comment removed for export] *)
